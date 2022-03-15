module InstructionDecoder

open Cpu
open Memory
open Value

type operand =
  | PC
  | Register: n:nat -> operand
  | Immediate: n:Cpu.word -> operand

type storage_operation =
  | Load: address:nat -> dest:nat -> storage_operation
  | Store: address:nat -> src:nat -> storage_operation

type cache_policy (n:memory_size) =
       (cache_state n) -> storage_operation -> (cache_state n)

let rec get_operands (#n #r: memory_size) (operands:list operand) (state:systemState #n #r): rv:(list (maybeBlinded #word)){FStar.List.length rv = FStar.List.length operands} =
  match operands with
    | Nil -> Nil
    | hd :: tl -> (match hd with
                  | PC -> Clear state.pc
                  | Register n -> if n < FStar.List.length state.registers then
                                    (FStar.List.Tot.index state.registers n)
                                 else Clear 0uL
                  | Immediate n -> Clear n
                ) :: get_operands tl state

let get_operands_with_one_operand_on_redacted_input_has_redacted_output (#n #r: memory_size) (op: operand) (state:systemState #n #r):
  Lemma (ensures get_operands [op] (redact_system state) = redact_list (get_operands [op] state) 0uL) =
  let head = FStar.List.Tot.hd (get_operands [op] state) in
  let head_of_redacted = FStar.List.Tot.hd (get_operands [op] (redact_system state)) in
  match op with
    | PC -> ()
    | Register n -> (
                   lists_are_equivalent_to_their_redaction _ state.registers 0uL;
                   equal_lists_are_equivalent _ (redact_system state).registers  (redact_list state.registers 0uL);
                   equivalent_lists_have_equal_lengths state.registers (redact_system state).registers;
                   if n >= FStar.List.length state.registers then ()
                   else ()
      )
    | Immediate n -> ()

let rec get_operands_on_redacted_input_has_redacted_output (#n #r: memory_size) (operands:list operand) (state:systemState #n #r):
  Lemma (ensures get_operands operands (redact_system state) = redact_list (get_operands operands state) 0uL)
        [SMTPat (get_operands operands (redact_system state))] =
  (
    match operands with
      | Nil -> ()
      | hd :: tl -> ( let head = FStar.List.Tot.hd (get_operands operands state) in
                    let head_of_redacted = FStar.List.Tot.hd (get_operands operands (redact_system state)) in

                    get_operands_with_one_operand_on_redacted_input_has_redacted_output hd state;
                    assert(redact head 0uL = head_of_redacted);

                    let redacted_head = redact head 0uL in

                    get_operands_on_redacted_input_has_redacted_output tl state;
                    assert(get_operands tl (redact_system state) = redact_list (get_operands tl state) 0uL);
                    assert((head_of_redacted :: (get_operands tl (redact_system state)))
                         = (redacted_head :: (redact_list (get_operands tl state) 0uL)))
                  )
)

let rec get_operands_on_equivalent_inputs_has_equivalent_output (#m #q #n #r: memory_size) (operands:list operand) (state1: systemState #m #q) (state2:systemState #n #r):
  Lemma (requires (equiv_system state1 state2))
        (ensures  (equiv_list (get_operands operands state1)
                              (get_operands operands state2)))
  = match operands with
      | Nil -> ()
      | hd :: tl -> (let result_hd1, result_hd2 = match hd with
                    | PC -> (
                         let head1 = FStar.List.Tot.hd (get_operands operands state1) in
                         let head2 = FStar.List.Tot.hd (get_operands operands state2) in
                         equal_values_are_equivalent Cpu.word head1 head2;
                         head1, head2
                         )
                    | Register n -> (
                        assert(equiv_list state1.registers state2.registers);
                        equivalent_lists_have_equal_lengths state1.registers state2.registers;
                        assert((FStar.List.length state1.registers) = (FStar.List.length state2.registers));
                        if n < FStar.List.length state1.registers then (
                          equivalent_lists_have_equivalent_values _ state1.registers state2.registers n )
                        else ();

                        FStar.List.Tot.hd (get_operands operands state1), FStar.List.Tot.hd (get_operands operands state2)
                        )
                    | Immediate n -> (Clear n, Clear n) in

                    assert(equiv result_hd1 result_hd2);
                    get_operands_on_equivalent_inputs_has_equivalent_output tl state1 state2
                  )

type decodedInstruction = { opcode: nat; input_operands: list operand; output_operands: list operand }

type decoder = (inst:word) -> decodedInstruction

type instruction_result (di:decodedInstruction) = {
  register_writes: (vals:(list (maybeBlinded #word)){FStar.List.length vals = FStar.List.length di.output_operands});
  memory_ops   :(list storage_operation)
  }

let equiv_storage_operation (lhs rhs: storage_operation) =
  match lhs, rhs with
    | (Load la ld), (Load ra rd) -> (la = ra /\ ld = rd)
    | (Store la ls), (Store ra rs) -> (la = ra /\ ls = rs)
    | _, _ -> False

let rec equiv_storage_operations (lhs rhs: list storage_operation) =
  match lhs, rhs with
    | lh :: lt, rh :: rt -> (equiv_storage_operation lh rh) /\ equiv_storage_operations lt rt
    | [], [] -> True
    | _, _ -> False

let equal_storage_operations_are_equivalent (lhs rhs: storage_operation):
  Lemma (requires lhs = rhs)
        (ensures  (equiv_storage_operation lhs rhs)) =
  ()

let rec equal_storage_operation_lists_are_equivalent (lhs rhs: list storage_operation):
  Lemma (requires lhs = rhs)
        (ensures equiv_storage_operations lhs rhs) =
  match lhs, rhs with
    | hl :: tl, hr :: tr -> (
         equal_storage_operations_are_equivalent hl hr;
         equal_storage_operation_lists_are_equivalent tl tr
      )
    | _ -> ()

let storage_operation_equivalence_is_symmetric (lhs rhs: storage_operation):
  Lemma (requires (equiv_storage_operation lhs rhs))
        (ensures  (equiv_storage_operation rhs lhs)) =
  ()

let rec storage_operation_list_equivalence_is_symmetric (lhs rhs: list storage_operation):
  Lemma (requires (equiv_storage_operations lhs rhs))
        (ensures  (equiv_storage_operations rhs lhs)) =
  match lhs, rhs with
   | hl :: tl, hr :: tr -> (
        storage_operation_equivalence_is_symmetric hl hr;
        storage_operation_list_equivalence_is_symmetric tl tr
     )
   | _ -> ()

let storage_operation_equivalence_is_transitive (lhs mid rhs: storage_operation):
  Lemma (requires (equiv_storage_operation lhs mid) /\ (equiv_storage_operation mid rhs))
        (ensures  (equiv_storage_operation lhs rhs)) =
  ()

let rec storage_operation_list_equivalence_is_transitive (lhs mid rhs: list storage_operation):
  Lemma (requires (equiv_storage_operations lhs mid) /\ (equiv_storage_operations mid rhs))
        (ensures  (equiv_storage_operations lhs rhs)) =
  match lhs, mid, rhs with
   | hl :: tl, hm :: tm, hr :: tr -> (
        storage_operation_equivalence_is_transitive hl hm hr;
        storage_operation_list_equivalence_is_transitive tl tm tr
     )
   | _ -> ()

let rec equivalent_storage_operation_lists_have_equal_length (lhs rhs: list storage_operation):
  Lemma (requires equiv_storage_operations lhs rhs)
        (ensures (FStar.List.length lhs) = (FStar.List.length rhs)) =
  match lhs, rhs with
    | hl :: tl, hr :: tr -> equivalent_storage_operation_lists_have_equal_length tl tr
    | _, _ -> ()


let equiv_result (#di:decodedInstruction) (lhs rhs:(instruction_result di)) =
    (equiv_list lhs.register_writes rhs.register_writes)
  /\ (equiv_storage_operations lhs.memory_ops rhs.memory_ops)

let equal_results_are_equivalent (#di:decodedInstruction) (lhs rhs:(instruction_result di)):
  Lemma (requires lhs = rhs)
        (ensures  equiv_result lhs rhs)
  = equal_lists_are_equivalent word lhs.register_writes rhs.register_writes;
    equal_storage_operation_lists_are_equivalent lhs.memory_ops rhs.memory_ops

let result_equivalence_is_symmetric (#di:decodedInstruction) (lhs rhs:(instruction_result di)):
  Lemma (requires equiv_result lhs rhs)
        (ensures equiv_result rhs lhs) =
  list_equivalence_is_symmetric word lhs.register_writes rhs.register_writes;
  storage_operation_list_equivalence_is_symmetric lhs.memory_ops rhs.memory_ops

let result_equivalence_is_transitive (#di:decodedInstruction) (lhs mid rhs:(instruction_result di)):
  Lemma (requires (equiv_result lhs mid) /\ (equiv_result mid rhs))
        (ensures  (equiv_result lhs rhs)) =
  list_equivalence_is_transitive word lhs.register_writes mid.register_writes rhs.register_writes;
  storage_operation_list_equivalence_is_transitive lhs.memory_ops mid.memory_ops rhs.memory_ops

type instruction_input (#n #r: memory_size) (di:decodedInstruction) =
     pre:(list (maybeBlinded #word)){(exists(s: systemState #n #r). pre = get_operands di.input_operands s)
                                    /\ FStar.List.length pre = FStar.List.length di.input_operands}


let redacted_instruction_inputs_are_instruction_inputs  (#n #r: memory_size) (di:decodedInstruction) (pre:instruction_input #n #r di): instruction_input #n #r di
  = assert(exists (s:systemState). (pre = get_operands #n #r di.input_operands s /\
             (get_operands #n #r di.input_operands (redact_system s) = redact_list (get_operands di.input_operands s) 0uL  )  ) );
    redact_list pre 0uL

type decoder_output (d:decoder) = (di:decodedInstruction{exists(inst:word). di = d inst})

type instruction_semantics (#n #r: memory_size) (d:decoder) = (di: decoder_output d) -> (pre:instruction_input #n #r di) -> instruction_result di

let is_redacting_equivalent_instruction_semantics_somewhere
      (#n #r: memory_size)
      (d:decoder)
      (s:instruction_semantics #n #r d)
      (inst:word)
      (input:instruction_input #n #r (d inst)) =
    redaction_preserves_length word input 0uL;
    let redacted_input = redacted_instruction_inputs_are_instruction_inputs (d inst) input in
    (equiv_result (s (d inst) input) (s (d inst) redacted_input))

let is_redacting_equivalent_instruction_semantics_everywhere (#n #r: memory_size) (d:decoder) (s:instruction_semantics #n #r d) =
    forall (inst:word) (pre:instruction_input #n #r (d inst)).
                is_redacting_equivalent_instruction_semantics_somewhere d s inst pre

let redacting_equivalent_instruction_semantics_on_equivalent_inputs_yields_equivalent_results_somewhere
      (#n #r: memory_size)
      (d:decoder)
      (s:instruction_semantics #n #r d)
      (inst:word)
      (input1 input2:instruction_input #n #r (d inst)):
  Lemma (requires (is_redacting_equivalent_instruction_semantics_everywhere d s) /\ (equiv_list input1 input2))
        (ensures  equiv_result (s (d inst) input1) (s (d inst) input2)) =
  let result1 = (s (d inst) input1) in
  let result2 = (s (d inst) input2) in
  let redacted_result1 = (s (d inst) (redact_list input1 0uL)) in
  let redacted_result2 = (s (d inst) (redact_list input2 0uL)) in

  equivalent_lists_have_equal_redactions word input1 input2 0uL;
  assert(redacted_result1 = redacted_result2);
  equal_results_are_equivalent redacted_result1 redacted_result2;

  result_equivalence_is_symmetric result2 redacted_result1;

  assert(equiv_result result1 redacted_result1);
  assert(equiv_result redacted_result1 result2);

  result_equivalence_is_transitive result1 redacted_result1 result2;
  assert(equiv_result result1 result2)


let rec mux_list_single (a:list(maybeBlinded #word)) (b:list(maybeBlinded #word)) (n:nat):
        list(maybeBlinded #word)
  = match a, b with
    | Nil, Nil -> Nil
    | hd :: tl, Nil -> a
    | Nil,     _ -> Nil
    | hd1 :: tl1, hd2 :: tl2 ->  if (n > 0)
                              then
                                hd1 :: (mux_list_single a b (n - 1))
                              else
                                hd2 :: tl1

let rec replace_list_value (orig:list(maybeBlinded #word)) (n:nat) (v:maybeBlinded #word):
        r:(list(maybeBlinded #word)){FStar.List.length r = FStar.List.length orig}
    = match orig with
      | Nil -> Nil
      | hd :: tl ->  if (n > 0)
                   then
                     hd :: (replace_list_value tl (n - 1) v)
                   else
                     v :: tl

let rec replacing_in_equivalent_lists_with_equivalent_value_yields_equivalent_lists (orig1 orig2:list(maybeBlinded #word)) (n:nat) (v1 v2:maybeBlinded #word):
  Lemma (requires (equiv_list orig1 orig2) /\ (equiv v1 v2))
        (ensures (equiv_list (replace_list_value orig1 n v1) (replace_list_value orig2 n v2))) =
  match n, orig1, orig2 with
    | 0, _, _ -> ()
    | _, h1 :: t1, h2 :: t2 -> replacing_in_equivalent_lists_with_equivalent_value_yields_equivalent_lists t1 t2 (n-1) v1 v2
    | _ -> ()

let rec replacing_then_reading_yields_original_value (orig: list (maybeBlinded #word)) (v:maybeBlinded #word) (n:nat):
  Lemma (requires n < FStar.List.length orig)
        (ensures FStar.List.Tot.index (replace_list_value orig n v) n = v)
    = match n, orig with
      | _, [] -> ()
      | 0, _ -> ()
      | _, hd :: tl -> replacing_then_reading_yields_original_value tl v (n-1)

let set_one_operand (#n #r: memory_size) (operand:operand) (value:maybeBlinded #word) (state:systemState #n #r): systemState #n #r =
    match operand with
      | PC -> (match value with
               | Clear v -> if FStar.UInt64.v v < FStar.List.length state.memory then
                              { state with pc = v }
                           else
                              { state with pc = 0uL }
               | Blinded b -> {state with pc = 0uL})
      | Register n -> if n < FStar.List.length state.registers then
                        { state with registers =
                          replace_list_value state.registers n value
                        }
                     else
                       state
      | Immediate n -> state

let setting_and_getting_one_non_faulting_operand_value_yields_original_value (#n #r: memory_size) (operand:operand) (value:maybeBlinded #word) (state:systemState #n #r):
  Lemma (requires ~(match operand with
                     | PC -> (match value with
                              | Blinded v -> True
                              | Clear v -> FStar.UInt64.v v >= FStar.List.length state.memory)
                     | Register n -> n >= FStar.List.length state.registers
                     | Immediate n -> True))
        (ensures get_operands [operand] (set_one_operand operand value state) = [value]) =
  let r = get_operands [operand] (set_one_operand operand value state) in
  match operand with
    | PC -> ()
    | Register n -> replacing_then_reading_yields_original_value state.registers value n


let setting_single_equivalent_operand_values_on_equivalent_systems_yields_equivalent_systems
    (#n #r: memory_size)
    (operand       :operand)
    (value1 value2 :(maybeBlinded #word))
    (state1 state2 :systemState #n #r):
    Lemma (requires (equiv_system state1 state2) /\ (equiv value1 value2))
          (ensures  (equiv_system (set_one_operand operand value1 state1) (set_one_operand operand value2 state2))) =
    match operand with
      | PC -> (match value1, value2 with
               | Clear v1, Clear v2 -> (
                       assert(v1 = v2);
                       equivalent_lists_have_equal_lengths state1.memory state2.memory;
                       let post1 = (set_one_operand operand value1 state1) in
                       let post2 = (set_one_operand operand value2 state2) in
                       assert(post1.pc = post2.pc)
                       )
               | _, _ -> ())
      | Register n -> (
          equivalent_lists_have_equal_lengths state1.registers state2.registers;
          if n >= FStar.List.length state1.registers then ()
          else
            replacing_in_equivalent_lists_with_equivalent_value_yields_equivalent_lists state1.registers state2.registers n value1 value2
        )
      | Immediate n -> ()


let rec set_operands (#n #r: memory_size) (operands:list operand) (values:(list (maybeBlinded #word)){FStar.List.length operands = FStar.List.length values}) (state:systemState #n #r): systemState #n #r =
    match operands, values with
      | o :: tl_o, v :: tl_v -> set_operands tl_o tl_v (set_one_operand o v state)
      | _ -> state

#set-options "--z3rlimit 1000"
let rec setting_equivalent_operand_values_on_equivalent_systems_yields_equivalent_systems
    (#n #r: memory_size)
    (operands       :list operand)
    (values1:(list (maybeBlinded #word)){FStar.List.length operands = FStar.List.length values1})
    (values2:(list (maybeBlinded #word)){FStar.List.length operands = FStar.List.length values2})
    (state1: systemState #n #r)  (state2 :systemState #n #r):
    Lemma (requires (equiv_system state1 state2) /\ (equiv_list values1 values2))
          (ensures  (equiv_system (set_operands operands values1 state1) (set_operands operands values2 state2))) =
    match operands, values1, values2 with
      | ho :: to, hv1 :: tv1, hv2 :: tv2 -> (
          assert(equiv hv1 hv2);

          let applied_head1 = set_one_operand ho hv1 state1 in
          let applied_head2 = set_one_operand ho hv2 state2 in
          setting_single_equivalent_operand_values_on_equivalent_systems_yields_equivalent_systems ho hv1 hv2 state1 state2;
          assert(equiv_system applied_head1 applied_head2);

          let applied_tail1 = (set_operands to tv1 applied_head1) in
          let applied_tail2 = (set_operands to tv2 applied_head2) in
          setting_equivalent_operand_values_on_equivalent_systems_yields_equivalent_systems to tv1 tv2 applied_head1 applied_head2;
          assert(equiv_system applied_tail1 applied_tail2)
        )
      | _ -> ()


let complete_one_memory_transaction (#n #r: memory_size) (op:storage_operation) (pre:systemState #n #r) (cp:cache_policy n): systemState #n #r =
  match op with
      | Load address register -> if register < FStar.List.length pre.registers
                                    && address < FStar.List.length pre.memory then
                                    { pre with registers = replace_list_value pre.registers register (FStar.List.Tot.index pre.memory address);
                                               cache_lines = cp pre.cache_lines op }
                                 else pre
      | Store address register -> if register < FStar.List.length pre.registers
                                    && address < FStar.List.length pre.memory then
                                    { pre with memory = replace_list_value pre.memory address (FStar.List.Tot.index pre.registers register);
                                               cache_lines = cp pre.cache_lines op }
                                 else pre

let rec complete_memory_transactions (#n #r: memory_size) (op:list storage_operation) (pre:systemState #n #r) (cp:cache_policy n) =
  match op with
    | hd :: tl -> (let post = (complete_one_memory_transaction hd pre cp) in
                 complete_memory_transactions tl post cp)
    | [] -> pre

let completing_single_memory_transactions_on_equivalent_systems_yields_equivalent_systems
    (#m #q #n #r: memory_size)
    (op1:storage_operation) (op2:storage_operation)
    (state1:systemState #m #q) (state2 :systemState #n #r)
    (cp:cache_policy m):
    Lemma (requires (equiv_system state1 state2) /\ (equiv_storage_operation op1 op2))
          (ensures  (equiv_system (complete_one_memory_transaction op1 state1 cp) (complete_one_memory_transaction op2 state2 cp))) =
                 let post1 = (complete_one_memory_transaction op1 state1 cp) in
                 let post2 = (complete_one_memory_transaction op2 state2 cp) in

                 assert(m = n /\ q = r);
                 assert(state1.cache_lines = state2.cache_lines);
                 assert(post1.cache_lines = post2.cache_lines);

                 equivalent_lists_have_equal_lengths state1.memory state2.memory;
                 equivalent_lists_have_equal_lengths state1.registers state2.registers;


                 match op1, op2 with
                  | Load a1 r1, Load a2 r2 -> (
                         assert(a1 = a2);
                         assert(r1 = r2);

                         assert(equiv_list state1.registers state2.registers);
                         assert(equiv_list state1.memory    state2.memory);


                         if (a1 < FStar.List.length state1.memory) && (r1 < FStar.List.length state1.registers) then (

                           assert(a2 < FStar.List.length state2.memory);
                           assert(r2 < FStar.List.length state2.registers);

                           equivalent_lists_have_equivalent_values word state1.memory state2.memory a1;
                           let write1 = (FStar.List.Tot.index state1.memory a1) in
                           let write2 = (FStar.List.Tot.index state2.memory a2) in
                           assert(equiv write1 write2);

                           assert(post1.registers = (replace_list_value state1.registers r1 write1));
                           assert(post2.registers = (replace_list_value state2.registers r2 write2));
                           replacing_in_equivalent_lists_with_equivalent_value_yields_equivalent_lists state1.registers state2.registers r1 write1 write2;
                           assert(equiv_list post1.registers post2.registers);
                           assert(equiv_list state1.memory state2.memory);
                           assert(post1.pc = post2.pc)
                           )
                         else (
                           assert(post1 = state1);
                           assert(post2 = state2)
                           );
                         assert(equiv_system post1 post2)
                    )
                  | Store a1 r1, Store a2 r2 -> (
                         assert(a1 = a2);
                         assert(r1 = r2);

                         assert(equiv_list state1.registers state2.registers);
                         assert(equiv_list state1.memory    state2.memory);

                         if (a1 < FStar.List.length state1.memory) && (r1 < FStar.List.length state1.registers) then (

                           assert(a2 < FStar.List.length state2.memory);
                           assert(r2 < FStar.List.length state2.registers);

                           equivalent_lists_have_equivalent_values word state1.registers state2.registers r1;
                           let write1 = (FStar.List.Tot.index state1.registers r1) in
                           let write2 = (FStar.List.Tot.index state2.registers r2) in
                           assert(equiv write1 write2);

                           assert(post1.memory = (replace_list_value state1.memory a1 write1));
                           assert(post2.memory = (replace_list_value state2.memory a2 write2));
                           replacing_in_equivalent_lists_with_equivalent_value_yields_equivalent_lists state1.memory state2.memory a1 write1 write2;
                           assert(equiv_list post1.registers post2.registers);
                           assert(equiv_list state1.memory state2.memory);
                           assert(post1.pc = post2.pc)
                           )
                         else (
                           assert(post1 = state1);
                           assert(post2 = state2)
                           );
                          assert(equiv_system post1 post2)
                    );
                 assert(equiv_system post1 post2)

let rec completing_equivalent_memory_transactions_on_equivalent_systems_yields_equivalent_systems
    (#m #q #n #r: memory_size)
    (ops1:list storage_operation) (ops2:(list storage_operation){FStar.List.length ops1 = FStar.List.length ops2})
    (state1:systemState #m #q) (state2 :systemState #n #r)
    (cp: cache_policy m):
    Lemma (requires (equiv_system state1 state2) /\ (equiv_storage_operations ops1 ops2))
          (ensures  (equiv_system (complete_memory_transactions ops1 state1 cp) (complete_memory_transactions ops2 state2 cp))) =
    assert(m = n /\ q = r);
    match ops1, ops2 with
     | op1 :: t1, op2 :: t2 -> (
           let post1 = complete_one_memory_transaction op1 state1 cp in
           let post2 = complete_one_memory_transaction op2 state2 cp in
           completing_single_memory_transactions_on_equivalent_systems_yields_equivalent_systems op1 op2 state1 state2 cp;
           completing_equivalent_memory_transactions_on_equivalent_systems_yields_equivalent_systems t1 t2 post1 post2 cp
       )
     | [], [] -> ()

let rec any_value_is_blinded (values: list (maybeBlinded #word)): bool =
  match values with
    | Nil              -> false
    | Blinded(hd) :: _  -> true
    | Clear(hd)   :: tl -> any_value_is_blinded tl

let rec equivalent_memories_have_identical_any_blindedness (a b: list (maybeBlinded #word)):
  Lemma (requires (equiv_list a b))
        (ensures (any_value_is_blinded a) = (any_value_is_blinded b))
  = match a, b with
      | hl::tl, hr::tr -> equivalent_memories_have_identical_any_blindedness tl tr
      | _ -> ()

let rec blind_all_values (values: list (maybeBlinded #word)): r:(list (maybeBlinded #word)){FStar.List.length values = FStar.List.length r} =
    match values with
      | Nil              -> Nil
      | Blinded(hd) :: tl -> Blinded(hd) :: blind_all_values tl
      | Clear(hd)   :: tl -> Blinded(hd) :: blind_all_values tl

let rec blinding_all_values_blinds_each_value (values: list (maybeBlinded #word)) (n:nat{n < FStar.List.length values}):
  Lemma (ensures Blinded? (FStar.List.Tot.index (blind_all_values values) n))
        [SMTPat (Blinded? (FStar.List.Tot.index (blind_all_values values) n))] =
  match n, values with
    | 0, _   -> ()
    | _, Nil -> ()
    | n, hd :: tl -> blinding_all_values_blinds_each_value tl (n-1)


let rec blinding_all_values_is_idempotent (values: list (maybeBlinded #word)):
  Lemma (ensures (blind_all_values values) = blind_all_values (blind_all_values values)) =
    match values with
      | hd :: tl -> blinding_all_values_is_idempotent tl
      | _ -> ()

let rec blinding_all_values_blinds_all_values (values: list (maybeBlinded #word)):
  Lemma (ensures all_values_are_blinded _ (blind_all_values values))
        [SMTPat (blind_all_values values)] =
  match values with
    | hd :: tl -> blinding_all_values_blinds_all_values tl
    | _ -> ()

let rec equivalent_unblinded_lists_are_equal (a b: list (maybeBlinded #word)):
  Lemma (requires (equiv_list a b) /\ (~(any_value_is_blinded a) \/ ~(any_value_is_blinded b)))
        (ensures a = b) =
  match a, b with
    | h1 :: t1, h2 :: t2 -> equivalent_unblinded_lists_are_equal t1 t2
    | _ -> ()

let rec mux_list (a:list (maybeBlinded #word)) (b:(list (maybeBlinded #word))) (which_b:list nat): Tot (list (maybeBlinded #word)) (decreases which_b) =
  match which_b with
    | Nil -> a
    | index_to_change :: tl -> mux_list (mux_list_single a b index_to_change) b tl

let decoding_execution_unit (#n #r: memory_size) (d:decoder) (s:instruction_semantics #n #r d)  (cp: cache_policy n) (inst:word) (pre:systemState #n #r): systemState #n #r =
    let decoded = d inst in
    let input_operand_values = (get_operands decoded.input_operands pre) in
    let instruction_output = (s decoded input_operand_values) in
    let output_operand_values = instruction_output.register_writes in
    let pre_with_incremented_pc = { pre with pc = (
                                        if FStar.UInt64.v pre.pc < FStar.List.length pre.memory - 1 then
                                          FStar.UInt64.add pre.pc 1uL
                                        else
                                          0uL
                                        ) } in
    let intermediate_with_updated_registers = set_operands decoded.output_operands output_operand_values pre_with_incremented_pc in
    complete_memory_transactions instruction_output.memory_ops intermediate_with_updated_registers cp

irreducible let trigger (#n #r: memory_size) (d:decoder) (s:instruction_semantics #n #r d) (cp:cache_policy n) (inst:word) (pre:systemState #n #r) = False

let decoding_execution_unit_with_redacting_equivalent_instruction_semantics_is_redacting_equivalent_somewhere (#n #r: memory_size) (d:decoder) (s:(instruction_semantics #n #r d){is_redacting_equivalent_instruction_semantics_everywhere d s}) (cp:cache_policy n) (inst:word) (pre:systemState #n #r):
    Lemma (ensures (equiv_system (decoding_execution_unit d s cp inst pre)
                                 (decoding_execution_unit d s cp inst (redact_system pre))))
    [SMTPat (trigger d s cp inst pre)] =
      let decoded = d inst in
      let input_operand_values = (get_operands decoded.input_operands pre) in
      let redacted_input_operand_values = (get_operands decoded.input_operands (redact_system pre)) in
      (* let redacted_input_operand_values = (redact_list (get_operands decoded.input_operands pre) 0) in *)
      let instruction_output = (s decoded input_operand_values) in
      let redacted_instruction_output = (s decoded redacted_input_operand_values) in
      let pre_with_incremented_pc = { pre with pc = (
                                      if FStar.UInt64.v pre.pc < FStar.List.length pre.memory - 1 then
                                         FStar.UInt64.add pre.pc 1uL
                                      else
                                        0uL
                                      ) } in

      systems_are_equivalent_to_their_redaction pre;
      get_operands_on_equivalent_inputs_has_equivalent_output decoded.input_operands pre (redact_system pre);
      assert(equiv_list input_operand_values redacted_input_operand_values);

      redacting_equivalent_instruction_semantics_on_equivalent_inputs_yields_equivalent_results_somewhere d s inst input_operand_values redacted_input_operand_values;
      assert(equiv_result instruction_output redacted_instruction_output);

      lists_are_equivalent_to_their_redaction word input_operand_values 0uL;

      assert(equiv_list input_operand_values (get_operands decoded.input_operands (redact_system pre)));

      list_equivalence_is_transitive word redacted_input_operand_values input_operand_values (get_operands decoded.input_operands (redact_system pre));
      assert(equiv_list redacted_input_operand_values (get_operands decoded.input_operands (redact_system pre)));

      assert(equiv_list instruction_output.register_writes redacted_instruction_output.register_writes);

      let post1 = set_operands decoded.output_operands instruction_output.register_writes pre_with_incremented_pc in
      let post_redacted1 = set_operands decoded.output_operands redacted_instruction_output.register_writes (redact_system pre_with_incremented_pc) in

      systems_are_equivalent_to_their_redaction pre_with_incremented_pc;
      assert(equiv_system pre_with_incremented_pc (redact_system pre_with_incremented_pc));

      setting_equivalent_operand_values_on_equivalent_systems_yields_equivalent_systems
        decoded.output_operands instruction_output.register_writes
        redacted_instruction_output.register_writes
        pre_with_incremented_pc
        (redact_system pre_with_incremented_pc);

      assert(equiv_system post1 post_redacted1);

      let post2: systemState #n #r = complete_memory_transactions instruction_output.memory_ops post1 cp in
      let post_redacted2: systemState #n #r = complete_memory_transactions redacted_instruction_output.memory_ops post_redacted1 cp in

      assert(equiv_storage_operations instruction_output.memory_ops redacted_instruction_output.memory_ops);
      equivalent_storage_operation_lists_have_equal_length instruction_output.memory_ops redacted_instruction_output.memory_ops;

      completing_equivalent_memory_transactions_on_equivalent_systems_yields_equivalent_systems
        instruction_output.memory_ops
        redacted_instruction_output.memory_ops
        post1
        post_redacted1
        cp;

      assert(equiv_system post2 post_redacted2)

let decoding_execution_unit_with_redacting_equivalent_instruction_semantics_is_redacting_equivalent (#n #r: memory_size) (d:decoder) (s:(instruction_semantics #n #r d){is_redacting_equivalent_instruction_semantics_everywhere d s}) (cp:cache_policy n):
  Lemma (ensures forall(pre:systemState #n #r) (inst:word).
                 (equiv_system (decoding_execution_unit d s cp inst pre)
                               (decoding_execution_unit d s cp inst (redact_system pre)))
                 \/ (trigger d s cp inst pre) )
    = ()

let each_decoding_execution_unit_with_redacting_equivalent_instruction_semantics_is_safe (#n #r: memory_size) (d:decoder) (s:(instruction_semantics #n #r d){is_redacting_equivalent_instruction_semantics_everywhere d s}) (cp:cache_policy n):
  Lemma (ensures is_safe (decoding_execution_unit d s cp))
  = decoding_execution_unit_with_redacting_equivalent_instruction_semantics_is_redacting_equivalent d s cp;
    redacting_equivalent_execution_units_are_safe (decoding_execution_unit d s cp)
