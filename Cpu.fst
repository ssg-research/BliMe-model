(* Top-level CPU model *)
module Cpu

open InstructionDecoder
open Memory
open Value

type address = nat
type word = byte

type registerFile
     = { pc: address; value: maybeBlinded #word }

type systemState
     = { memory: memoryState; registers:registerFile  }

let equiv_system (lhs:systemState) (rhs:systemState)
    =    (lhs.registers.pc = rhs.registers.pc)
       /\ (equiv  lhs.registers.value rhs.registers.value)
       /\ (equiv_list lhs.memory rhs.memory)

let system_equivalence_is_transitive (lhs mid rhs:systemState):
    Lemma (requires (equiv_system lhs mid) /\ (equiv_system mid rhs))
          (ensures  equiv_system lhs rhs)
    = assert(lhs.registers.pc = rhs.registers.pc);
      equivalence_is_transitive      _ lhs.registers.value mid.registers.value rhs.registers.value;
      list_equivalence_is_transitive _ lhs.memory          mid.memory          rhs.memory

let system_equivalence_is_symmetric (lhs rhs:systemState):
    Lemma (requires equiv_system lhs rhs)
          (ensures  equiv_system rhs lhs)
    = assert(lhs.registers.pc = rhs.registers.pc);
      equivalence_is_symmetric _ lhs.registers.value rhs.registers.value;
      list_equivalence_is_symmetric _ lhs.memory          rhs.memory


let equal (lhs:systemState) (rhs:systemState)
    =   (lhs.registers.pc = rhs.registers.pc)
       /\ (lhs.registers.value = rhs.registers.value)
       /\ (lhs.memory = rhs.memory)


let redact_system (s:systemState): systemState = {
                                       registers = { s.registers with value = redact s.registers.value 0 };
                                       memory    = redact_list s.memory 0
                                   }


let systems_are_equivalent_to_their_redaction (s:systemState):
    Lemma (ensures equiv_system s (redact_system s))
    = values_are_equivalent_to_their_redaction _ s.registers.value 0;
      lists_are_equivalent_to_their_redaction  _ s.memory 0

let equivalent_systems_have_equal_redactions (s1:systemState) (s2:systemState):
    Lemma (ensures (equiv_system s1 s2) <==> ((redact_system s1) == (redact_system s2)))
    = equivalent_values_have_equal_redactions _ s1.registers.value s2.registers.value 0;
      equivalent_lists_have_equal_redactions  _ s1.memory s2.memory 0

      (*
let _ = assert(forall (s1:systemState) (s2:systemState) (f: systemState -> systemState).
                 (equal s1 s2) ==> (let t1, t2 = f s1, f s2 in (
                          (s1.registers.pc    == s2.registers.pc)
                        /\ (s1.registers.value == s2.registers.value)
                        /\ (t1.registers.pc    == t2.registers.pc)
                        /\ (t1.registers.value == t2.registers.value)
                          (equal (f s1) (f s2))
                 ))
              )

   *)
      (*
let _ = assert(forall (x y z: systemState). ( (equal x y) /\ (equal y z) ==> (equal x z)) )
  *)

type execution_unit = word -> systemState -> systemState

val step
    (exec:execution_unit)
    (pre_state: systemState)
    : systemState

let step exec pre_state =
    let instruction = nth pre_state.registers.pc pre_state.memory in
        match instruction with
        | Blinded _ -> pre_state
        | Clear inst -> exec inst pre_state

let is_safe_single_step (exec:execution_unit) (pre:systemState) =
    (equiv_system (step exec pre) (step exec (redact_system pre)))

let is_safe_execution_unit_single_step (exec:execution_unit) =
        forall (pre:systemState). is_safe_single_step exec pre

let all_single_steps_safe_mean_execution_unit_is_safe  (exec:execution_unit):
    Lemma (requires forall (pre:systemState). (is_safe_single_step exec pre))
          (ensures  is_safe_execution_unit_single_step exec)
          = ()


type single_step_safe_execution_unit = e:execution_unit{is_safe_execution_unit_single_step e}

let equivalent_inputs_yield_equivalent_states (exec:execution_unit) (pre1 pre2 : systemState) =
            equiv_system pre1 pre2 ==> equiv_system (step exec pre1) (step exec pre2)

let is_safe (exec:execution_unit) =
  forall (pre1 pre2 : systemState). equivalent_inputs_yield_equivalent_states exec pre1 pre2


type safe_execution_unit = exec:execution_unit{is_safe exec}

let single_step_safe_execution_units_give_equivalent_outputs_for_equivalent_inputs
    (exec:execution_unit) (pre_1:systemState) (pre_2:systemState)
    : Lemma (requires (is_safe_execution_unit_single_step exec) /\ equiv_system pre_1 pre_2)
            (ensures equiv_system (step exec pre_1) (step exec pre_2))
      = equivalent_systems_have_equal_redactions pre_1 pre_2;
        assert( (step exec (redact_system pre_1)) == (step exec (redact_system pre_2)) );
        system_equivalence_is_symmetric (step exec pre_2) (step exec (redact_system pre_2));
        assert( equiv_system (step exec (redact_system pre_2)) (step exec pre_2) );
        system_equivalence_is_transitive (step exec pre_1) (step exec (redact_system pre_1)) (step exec pre_2)

let single_step_safe_execution_units_are_safe
      (exec:single_step_safe_execution_unit):
      Lemma (ensures is_safe exec)
      = assert( is_safe_execution_unit_single_step exec ) ;
        assert( forall (pre:systemState). is_safe_single_step exec pre ) ;
        assert( forall (pre1:systemState) (pre2: systemState{equiv_system pre1 pre2}). (equiv_system (step exec pre1) (step exec pre2)))


(* Now let's look at what the execution units should look like. *)
type redacting_execution_unit = exec:execution_unit{
     forall (inst:word) (pre:systemState). (equiv_system (exec inst pre) (exec inst (redact_system pre)))}


let redacting_execution_unit_is_everywhere_safe (pre1 pre2 : systemState) (exec:redacting_execution_unit):
  Lemma (requires equiv_system pre1 pre2)
        (ensures equiv_system (step exec pre1) (step exec pre2))
  = equivalent_systems_have_equal_redactions pre1 pre2;
    assert( (step exec (redact_system pre1)) == (step exec (redact_system pre2)) );
    assert( equiv_system (step exec pre2) (step exec (redact_system pre2)) ) ;
                                                admit() ;
    system_equivalence_is_symmetric (step exec pre2) (step exec (redact_system pre2));
    assert( equiv_system (step exec (redact_system pre2)) (step exec pre2) );
    system_equivalence_is_transitive (step exec pre1) (step exec (redact_system pre1)) (step exec pre2)

let redacting_execution_unit_is_single_step_safe (exec:redacting_execution_unit)
  : Lemma (ensures is_safe exec)
  = ()
