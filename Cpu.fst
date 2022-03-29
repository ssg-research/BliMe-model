/// *******************
/// Low-level CPU model
/// *******************
module Cpu

open Memory
open Value

/// ============
/// System state
/// ============

/// We start by defining the low-level state of the system.  We begin by defining memory
/// types.
///
/// What does an address look like, and what does a word in memory look like?
type address = FStar.UInt64.t
type word = FStar.UInt64.t

/// Furthermore what is the size of the memory?  Since an address is a UInt64, the
/// memory should have at most :math:`2^{64}` cells.
type memory_size = n:int{FStar.UInt.fits n FStar.UInt64.n}

/// Next we describe the state of the caches.  We don't need to include the
/// actual cache lines; for our purposes, an array of cache line assignments
/// is enough.
type cache_state (n:memory_size) =
       (list (a:address{FStar.UInt64.v a < n}))

/// Finally, we can define the state of the overall system.  This type is
/// parametrized by the sizes of the memory and register file, as described in
/// §6.2.2 of the paper.
type systemState (#n #r:memory_size)
     = { memory: (memory:memoryState{(FStar.List.length memory) = n});
    cache_lines: (list (a:address{FStar.UInt64.v a < n}));
             pc: (pc:word{FStar.UInt64.v pc < n});
      registers: (registers:memoryState{FStar.List.length registers = r})}

/// -----------
/// Equivalence
/// -----------
///
/// Next we define and analyze the notion of system equivalence, :math:`\stackrel{\mathrm{state}}{\equiv}`, as in §6.2.2 of the paper.
///
/// Two systems are in equivalent states if
///   - their memory banks and register files have the same size,
///   - their program counters point to the same address,
///   - their cache line assignments are identical,
///   - their memory banks and register files are equivalent, in the sense of :ref:`equiv_list <equiv_list>`
///
/// .. fst::
///   :name: equiv_system
let equiv_system (#m #q #n #r: memory_size) (lhs:systemState #m #q) (rhs:systemState #n #r)
    = (m = n)
       /\ (q = r)
       /\ (lhs.pc = rhs.pc)
       /\ (equiv_list lhs.registers rhs.registers)
       /\ (equiv_list lhs.memory rhs.memory)
       /\ (equivalent_lists_have_equal_lengths lhs.memory rhs.memory;
          lhs.cache_lines = rhs.cache_lines)

/// We then prove several properties of :math:`\stackrel{\mathrm{state}}{\equiv}`:
///   - **Equality implies equivalence**: :math:`s_1 = s_2 \Rightarrow s_1 \stackrel{\mathrm{state}}{\equiv} s_2`
let equal_systems_are_equivalent (#n #r:memory_size) (lhs:systemState #n #r) (rhs:systemState #n #r):
  Lemma (requires lhs = rhs) (ensures (equiv_system #n #r #n #r lhs rhs)) =
  equal_lists_are_equivalent _ lhs.registers rhs.registers;
  equal_lists_are_equivalent _ lhs.memory rhs.memory

///   - **Transitivity**: :math:`s_1 \stackrel{\mathrm{state}}{\equiv} s_2 \wedge s_2 \stackrel{\mathrm{state}}{\equiv} s_3 \Rightarrow s_1 \stackrel{\mathrm{state}}{\equiv} s_3`
let system_equivalence_is_transitive (#m #q #n #r #o #s: memory_size)
                                     (lhs:systemState #m #q)
                                     (mid:systemState #n #r)
                                     (rhs:systemState #o #s):
    Lemma (requires (equiv_system lhs mid) /\ (equiv_system mid rhs))
          (ensures  equiv_system lhs rhs)
    = assert(lhs.pc = rhs.pc);

      list_equivalence_is_transitive _ lhs.registers mid.registers rhs.registers;
      list_equivalence_is_transitive _ lhs.memory          mid.memory          rhs.memory;

      equivalent_lists_have_equal_lengths lhs.memory rhs.memory;
      assert(lhs.cache_lines = rhs.cache_lines)


///   - **Symmetry**: :math:`s_1 \stackrel{\mathrm{state}}{\equiv} s_2 \Leftrightarrow s_2 \stackrel{\mathrm{state}}{\equiv} s_1`
let system_equivalence_is_symmetric (#m #q #n #r: memory_size)
                                    (lhs: systemState #m #q)
                                    (rhs:systemState #n #r):
    Lemma (requires equiv_system lhs rhs)
          (ensures  equiv_system rhs lhs)
    = assert(lhs.pc = rhs.pc);

      equivalent_lists_have_equal_lengths lhs.memory rhs.memory;
      assert(lhs.cache_lines = rhs.cache_lines);

      list_equivalence_is_symmetric _ lhs.registers rhs.registers;
      list_equivalence_is_symmetric _ lhs.memory          rhs.memory

/// ---------
/// Redaction
/// ---------
///
/// Equivalence is not always the easiest notion to work with, since the
/// associated theorems often take the form of
///
/// .. math ::
///
///    \forall s_1, s_2. s_1 \stackrel{\mathrm{state}}{\equiv} s_2 \Rightarrow f(s_1) \stackrel{\mathrm{state}}{\equiv} f(s_2),
///
/// which we need to prove despite not knowing anything about :math:`s_1`
/// or :math:`s_2` or their relationship to one another.
///
/// We introduce the concept of *redaction*, which is to zero all of the data in
/// blinded values of the system.
let redact_system (#n #r: memory_size) (s:systemState #n #r): systemState #n #r = {
    pc = (redaction_preserves_length _ s.memory 0uL;
          let redacted_memory = redact_list s.memory 0uL in
          s.pc);
    cache_lines = s.cache_lines;
    registers = (redaction_preserves_length _ s.registers 0uL;
                 redact_list s.registers 0uL);
    memory    = redact_list s.memory 0uL
    }

/// We then prove that systems are equivalent to their redaction:
let systems_are_equivalent_to_their_redaction (#n #r: memory_size) (s:systemState #n #r):
    Lemma (ensures equiv_system s (redact_system s))
    = lists_are_equivalent_to_their_redaction  _ s.registers 0uL;
      lists_are_equivalent_to_their_redaction  _ s.memory 0uL

/// and that the redactions of equivalent systems are equal:

let equivalent_systems_have_equal_redactions (#m #q #n #r: memory_size)
                                             (s1:systemState #m #q)
                                             (s2:systemState #n #r):
    Lemma (requires (equiv_system s1 s2)) (ensures ((redact_system s1) == (redact_system s2)))
    = assert(m = n);
      equivalent_lists_have_equal_redactions _ s1.registers s2.registers 0uL;
      equivalent_lists_have_equal_redactions _ s1.memory s2.memory 0uL

/// Together, these theorems let us more easily prove theorems of the form
///
/// .. math ::
///
///     \forall s_1, s_2: s_1 \stackrel{\mathrm{state}}{\equiv} s_2 \Rightarrow f(s_1) \stackrel{\mathrm{state}}{\equiv} f(s_2).
///
/// by instead proving that
///
/// .. math ::
///
///    \forall s: f(s) \stackrel{\mathrm{state}}{\equiv} f(\mathrm{redact}\; s)
///
/// which by ``systems_are_equivalent_to_their_redaction`` and ``equivalent_systems_have_equal_redactions`` yield
///
/// .. math ::
///
///    \forall s_1, s_2: s_1 \stackrel{\mathrm{state}}{\equiv} s_2 \Rightarrow  f(s_1) \stackrel{\mathrm{state}}{\equiv} f(\mathrm{redact}\; s_1) = f(\mathrm{redact}\; s_2) \stackrel{\mathrm{state}}{\equiv} f(s_2) .
/// 


/// ===============
/// Execution model
/// ===============
///
/// The next step is to describe how the system actually executes.
///
/// We represent this using:
///   - an execution unit (essentially, an ISA)
///
///     .. fst ::
type execution_unit (#n #r:memory_size) = word -> systemState #n #r -> systemState #n #r

///   - a function that "steps" the processor state, which in this case
///     means to load an instruction from memory and execute it in a
///     single cycle.

val step (#n #r:memory_size)
    (exec:execution_unit #n #r)
    (pre_state: systemState #n #r)
    : systemState #n #r

let step exec pre_state =
    let instruction = Memory.nth pre_state.memory pre_state.pc in
        match instruction with
        | Blinded _ -> { pre_state with pc = 0uL }
        | Clear inst -> exec inst pre_state


/// ==================
/// Safety definitions
/// ==================
///
/// ------------------------
/// Equivalence-based safety
/// ------------------------
///
/// We define safety in this case to be that the system is safe if executing on
/// equivalent (and so indistinguishable) states always results in equivalent
/// output states.
///
/// We start by defining a test that checks whether this is the case for a
/// particular set of equivalent initial states:

let equivalent_inputs_yield_equivalent_states (#n #r:memory_size)
                                              (exec:execution_unit #n #r)
                                              (pre1:systemState #n #r)
                                              (pre2:(systemState #n #r){equiv_system pre1 pre2}) =
    equiv_system (step exec pre1) (step exec pre2)

/// Then, we define safety by whether execution preserves state equivalence for
/// *all* possible inputs.
let is_safe (#n #r:memory_size) (exec:execution_unit #n #r) =
    forall (pre1 pre2 : systemState). (equiv_system pre1 pre2) ==> equivalent_inputs_yield_equivalent_states exec pre1 pre2

type safe_execution_unit (#n #r:memory_size) = exec:(execution_unit #n #r){is_safe exec}

/// ----------------------
/// Redaction-based safety
/// ----------------------
/// We can show that a system constructed from an execution unit that produces
/// an equivalent output when operating on the same input but with the blinded
/// values zeroed is safe.

 let is_redacting_equivalent_execution_unit (#n #r:memory_size) (exec:execution_unit #n #r)
   = forall(pre:systemState) (inst:word).  (equiv_system (exec inst pre) (exec inst (redact_system pre)))

type redacting_equivalent_execution_unit (#n #r:memory_size)
   = exec:(execution_unit #n #r){is_redacting_equivalent_execution_unit exec}

let is_redacting_equivalent_system_single_step_somewhere (#n #r:memory_size)
                                                         (exec:execution_unit #n #r)
                                                         (pre:systemState #n #r) =
    (equiv_system (step exec pre) (step exec (redact_system pre)))

let is_redacting_equivalent_system_single_step_everywhere (#n #r:memory_size)
                                                          (exec:execution_unit #n #r) =
    forall (pre:systemState). is_redacting_equivalent_system_single_step_somewhere exec pre

let redacting_equivalent_execution_units_lead_to_redacting_equivalent_systems_somewhere
                                                          (#n #r:memory_size)
                                                          (exec:redacting_equivalent_execution_unit #n #r)
                                                          (pre:systemState #n #r):
    Lemma (ensures is_redacting_equivalent_system_single_step_somewhere exec pre) =
      let redaction = redact_system pre in
      systems_are_equivalent_to_their_redaction pre;
      assert(pre.pc = redaction.pc);
      let pc = pre.pc in
      equivalent_memories_have_equivalent_values pre.memory redaction.memory pc;
      assert(equiv_list pre.memory redaction.memory);
      assert(equiv (Memory.nth pre.memory pc) (Memory.nth redaction.memory pc))

let redacting_equivalent_systems_give_equivalent_outputs_for_equivalent_inputs (#n #r:memory_size)
    (exec:redacting_equivalent_execution_unit #n #r) (pre_1:systemState #n #r) (pre_2:systemState #n #r)
      : Lemma (requires equiv_system pre_1 pre_2)
              (ensures equiv_system (step exec pre_1) (step exec pre_2))
              [SMTPat (equiv_system (step exec pre_1) (step exec pre_2))]
      = redacting_equivalent_execution_units_lead_to_redacting_equivalent_systems_somewhere exec pre_1;
        redacting_equivalent_execution_units_lead_to_redacting_equivalent_systems_somewhere exec pre_2;
        equivalent_systems_have_equal_redactions pre_1 pre_2;
        assert( (step exec (redact_system pre_1)) == (step exec (redact_system pre_2)) );
        system_equivalence_is_symmetric (step exec pre_2) (step exec (redact_system pre_2));
        assert( equiv_system (step exec (redact_system pre_2)) (step exec pre_2) );
        system_equivalence_is_transitive (step exec pre_1)
                                         (step exec (redact_system pre_1))
                                         (step exec pre_2)

/// ------------
/// Main theorem
/// ------------
let redacting_equivalent_execution_units_are_safe (#n #r:memory_size)
    (exec:redacting_equivalent_execution_unit #n #r):
    Lemma (ensures is_safe exec)
      = ()

