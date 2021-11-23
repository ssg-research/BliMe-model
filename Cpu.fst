(* Top-level CPU model *)
module Cpu

open Memory
open Value

type address = FStar.UInt64.t
type word = FStar.UInt64.t

type systemState
     = { memory: (memory:memoryState{FStar.UInt.fits (FStar.List.length memory) FStar.UInt64.n});
             pc: (pc:word{FStar.UInt64.v pc < FStar.List.length memory});
      registers: memoryState}

(* Equivalence *)
let equiv_system (lhs:systemState) (rhs:systemState)
    =    (lhs.pc = rhs.pc)
       /\ (equiv_list lhs.registers rhs.registers)
       /\ (equiv_list lhs.memory rhs.memory)

let equal_systems_are_equivalent (lhs:systemState) (rhs:systemState):
  Lemma (requires lhs = rhs) (ensures (equiv_system lhs rhs)) =
  equal_lists_are_equivalent _ lhs.registers rhs.registers;
  equal_lists_are_equivalent _ lhs.memory rhs.memory

let system_equivalence_is_transitive (lhs mid rhs:systemState):
    Lemma (requires (equiv_system lhs mid) /\ (equiv_system mid rhs))
          (ensures  equiv_system lhs rhs)
    = assert(lhs.pc = rhs.pc);
      list_equivalence_is_transitive _ lhs.registers mid.registers rhs.registers;
      list_equivalence_is_transitive _ lhs.memory          mid.memory          rhs.memory

let system_equivalence_is_symmetric (lhs rhs:systemState):
    Lemma (requires equiv_system lhs rhs)
          (ensures  equiv_system rhs lhs)
    = assert(lhs.pc = rhs.pc);
      list_equivalence_is_symmetric _ lhs.registers rhs.registers;
      list_equivalence_is_symmetric _ lhs.memory          rhs.memory


(*******************************************************************************
 * Redaction
 *
 * We introduce the concept of "redaction", which is to zero all of the data in
 * blinded values of the system.
 *******************************************************************************)

let redact_system (s:systemState): systemState = {
    pc = (redaction_preserves_length _ s.memory 0uL;
          let redacted_memory = redact_list s.memory 0uL in
          s.pc);
    registers = (redaction_preserves_length _ s.registers 0uL;
                 redact_list s.registers 0uL);
    memory    = redact_list s.memory 0uL
    }


let systems_are_equivalent_to_their_redaction (s:systemState):
    Lemma (ensures equiv_system s (redact_system s))
    = lists_are_equivalent_to_their_redaction  _ s.registers 0uL;
      lists_are_equivalent_to_their_redaction  _ s.memory 0uL

let equivalent_systems_have_equal_redactions (s1:systemState) (s2:systemState):
    Lemma (ensures (equiv_system s1 s2) <==> ((redact_system s1) == (redact_system s2)))
    = equivalent_lists_have_equal_redactions _ s1.registers s2.registers 0uL;
      equivalent_lists_have_equal_redactions _ s1.memory s2.memory 0uL


(*******************************************************************************
 * System definition.
 *
 * We build our system from an execution unit (essentially, an ISA)
 * and a function that "steps" the processor state (essentially, the
 * microarchitecture, which for now just fetch-executes in a single step).
 *******************************************************************************)
type execution_unit = word -> systemState -> systemState

val step
    (exec:execution_unit)
    (pre_state: systemState)
    : systemState

let step exec pre_state =
    let instruction = Memory.nth pre_state.memory pre_state.pc in
        match instruction with
        | Blinded _ -> pre_state
        | Clear inst -> exec inst pre_state

(*******************************************************************************
 * Equivalence-based safety.
 *
 * We define safety in this case to be that the system is safe if executing on
 * equivalent (and so indistinguishable) states always results in equivalent
 * output states.
 *******************************************************************************)
let equivalent_inputs_yield_equivalent_states (exec:execution_unit) (pre1 pre2 : systemState) =
    equiv_system pre1 pre2 ==> equiv_system (step exec pre1) (step exec pre2)

let is_safe (exec:execution_unit) =
    forall (pre1 pre2 : systemState). equivalent_inputs_yield_equivalent_states exec pre1 pre2

type safe_execution_unit = exec:execution_unit{is_safe exec}

(*******************************************************************************
 * Redacting-equivalent execution units.
 *
 * We can show that a system constructed from an execution unit that produces
 * an equivalent output when operating on the same input but with the blinded
 * values zeroed is safe.
 *******************************************************************************)

 let is_redacting_equivalent_execution_unit (exec:execution_unit)
   = forall(pre:systemState) (inst:word).  (equiv_system (exec inst pre) (exec inst (redact_system pre)))

type redacting_equivalent_execution_unit
   = exec:execution_unit{is_redacting_equivalent_execution_unit exec}

let is_redacting_equivalent_system_single_step_somewhere (exec:execution_unit) (pre:systemState) =
    (equiv_system (step exec pre) (step exec (redact_system pre)))

let is_redacting_equivalent_system_single_step_everywhere (exec:execution_unit) =
    forall (pre:systemState). is_redacting_equivalent_system_single_step_somewhere exec pre

let redacting_equivalent_execution_units_lead_to_redacting_equivalent_systems_somewhere
    (exec:redacting_equivalent_execution_unit) (pre:systemState):
    Lemma (ensures is_redacting_equivalent_system_single_step_somewhere exec pre) =
      let redaction = redact_system pre in
      systems_are_equivalent_to_their_redaction pre;
      assert(pre.pc = redaction.pc);
      let pc = pre.pc in
      equivalent_memories_have_equivalent_values pre.memory redaction.memory pc;
      assert(equiv_list pre.memory redaction.memory);
      assert(equiv (Memory.nth pre.memory pc) (Memory.nth redaction.memory pc))

let redacting_equivalent_systems_give_equivalent_outputs_for_equivalent_inputs
    (exec:redacting_equivalent_execution_unit) (pre_1:systemState) (pre_2:systemState)
      : Lemma (requires equiv_system pre_1 pre_2)
              (ensures equiv_system (step exec pre_1) (step exec pre_2))
              [SMTPat (equiv_system (step exec pre_1) (step exec pre_2))]
      = redacting_equivalent_execution_units_lead_to_redacting_equivalent_systems_somewhere exec pre_1;
        redacting_equivalent_execution_units_lead_to_redacting_equivalent_systems_somewhere exec pre_2;
        equivalent_systems_have_equal_redactions pre_1 pre_2;
        assert( (step exec (redact_system pre_1)) == (step exec (redact_system pre_2)) );
        system_equivalence_is_symmetric (step exec pre_2) (step exec (redact_system pre_2));
        assert( equiv_system (step exec (redact_system pre_2)) (step exec pre_2) );
        system_equivalence_is_transitive (step exec pre_1) (step exec (redact_system pre_1)) (step exec pre_2)

(* The main theorem about execution_units *)
let redacting_equivalent_execution_units_are_safe
    (exec:redacting_equivalent_execution_unit):
    Lemma (ensures is_safe exec)
      = ()

