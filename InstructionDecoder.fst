module InstructionDecoder

open Cpu
open Memory
open Value

type operand =
  | Register: n:nat -> operand
  | Memory:   n:nat -> operand

let rec get_operands (operands:list operand) (state:systemState): r:(list (maybeBlinded #word)){FStar.List.length r = FStar.List.length operands} =
  match operands with
    | Nil -> Nil
    | hd :: tl -> (match hd with
                  | Register n -> if n < FStar.List.length state.registers then
                                    (Memory.nth state.registers n)
                                 else Clear 0
                  | Memory   n -> if n < FStar.List.length state.memory then
                                    (Memory.nth state.memory n)
                                 else Clear 0
                ) :: get_operands tl state

let rec get_operands_on_redacted_input_has_equivalent_output (operands:list operand) (state:systemState):
  Lemma (ensures (equiv_list (get_operands operands state) (get_operands operands (redact_system state)) ))
  = let redacted_state = (redact_system state) in
    systems_are_equivalent_to_their_redaction state;
    match operands with
      | Nil -> ()
      | hd :: tl -> ((match hd with
                    | Register n -> (
                        lists_are_equivalent_to_their_redaction _ state.registers 0;
                        assert((FStar.List.length state.registers) = (FStar.List.length redacted_state.registers));
                        if n < FStar.List.length state.registers then (
                          equivalent_memories_have_equivalent_values state.registers redacted_state.registers n )
                        else ()
                        )
                    | Memory n -> (
                        lists_are_equivalent_to_their_redaction _ state.memory 0;
                        assert(FStar.List.length state.memory = FStar.List.length redacted_state.memory);
                        if n < FStar.List.length state.memory then (
                        equivalent_memories_have_equivalent_values state.memory redacted_state.memory n )
                        else ()
                        ));
                    get_operands_on_redacted_input_has_equivalent_output tl state
                  )

type decodedInstruction = { opcode: int; input_operands: list operand; output_operands: list operand }

type decoder = (inst:word) -> decodedInstruction

type instruction_semantics =
  (di: decodedInstruction) ->
  (pre:(list (maybeBlinded #word)){FStar.List.length pre = FStar.List.length di.input_operands}) ->
  (post:(list (maybeBlinded #word)){FStar.List.length post = FStar.List.length di.output_operands})

let is_redacting_equivalent_instruction_semantics_somewhere
      (s:instruction_semantics)
      (di:decodedInstruction)
      (input:(list (maybeBlinded #word)){FStar.List.length input = FStar.List.length di.input_operands}) =
    redaction_preserves_length word input 0;
    (equiv_list (s di input) (s di (redact_list input 0)))

let is_redacting_equivalent_instruction_semantics_everywhere (s:instruction_semantics) (di:decodedInstruction) =
    forall(pre:(list (maybeBlinded #word)){FStar.List.length pre = FStar.List.length di.input_operands}).
                is_redacting_equivalent_instruction_semantics_somewhere s di pre


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

let set_one_operand (operand:operand) (value:maybeBlinded #word) (state:systemState): systemState =
    match operand with
      | Register n -> if n < FStar.List.length state.registers then
                        { state with registers =
                          replace_list_value state.registers n value 
                        }
                     else
                       state
      | Memory n -> if n < FStar.List.length state.memory then
                      let modified_memory = replace_list_value state.memory n value in
                      assert(FStar.List.length modified_memory = FStar.List.length state.memory);
                      { state with memory = replace_list_value state.memory n value }
                   else
                     state

let setting_single_equivalent_operand_values_on_equivalent_systems_yields_equivalent_systems
    (operand       :operand)
    (value1 value2 :(maybeBlinded #word))
    (state1 state2 :systemState):
    Lemma (requires (equiv_system state1 state2) /\ (equiv value1 value2))
          (ensures  (equiv_system (set_one_operand operand value1 state1) (set_one_operand operand value2 state2))) =
    match operand with
      | Register n -> (
          equivalent_lists_have_equal_lengths state1.registers state2.registers;
          if n >= FStar.List.length state1.registers then ()
          else
            replacing_in_equivalent_lists_with_equivalent_value_yields_equivalent_lists state1.registers state2.registers n value1 value2
        )
      | Memory n -> (
          equivalent_lists_have_equal_lengths state1.memory state2.memory;
          if n >= FStar.List.length state1.memory then ()
          else
            replacing_in_equivalent_lists_with_equivalent_value_yields_equivalent_lists state1.memory state2.memory n value1 value2
        )


let rec set_operands (operands:list operand) (values:(list (maybeBlinded #word)){FStar.List.length operands = FStar.List.length values}) (state:systemState): systemState =
    match operands, values with
      | o :: tl_o, v :: tl_v -> set_operands tl_o tl_v (set_one_operand o v state)
      | _ -> state


let rec setting_equivalent_operand_values_on_equivalent_systems_yields_equivalent_systems
    (operands       :list operand)
    (values1:(list (maybeBlinded #word)){FStar.List.length operands = FStar.List.length values1})
    (values2:(list (maybeBlinded #word)){FStar.List.length operands = FStar.List.length values2})
    (state1  state2 :systemState):
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
  Lemma (ensures Blinded? (nth (blind_all_values values) n))
        [SMTPat (Blinded? (nth (blind_all_values values) n))] =
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

let decoding_execution_unit (d:decoder) (s:instruction_semantics) (inst:word) (pre:systemState): systemState =
    let decoded = d inst in
    let input_operand_values = (get_operands decoded.input_operands pre) in
    let output_operand_values = (s decoded input_operand_values) in
    let output_operand_values = if any_value_is_blinded input_operand_values then
                                   blind_all_values output_operand_values
                                else
                                  output_operand_values
                                in
    set_operands decoded.output_operands output_operand_values pre


irreducible let trigger (d:decoder) (s:instruction_semantics) (inst:word) (pre:systemState) = False

let decoding_execution_unit_is_redacting_equivalent_somewhere (d:decoder) (s:instruction_semantics) (inst:word) (pre:systemState):
    Lemma (ensures (equiv_system (decoding_execution_unit d s inst pre)
                                 (decoding_execution_unit d s inst (redact_system pre))))
          [SMTPat (trigger d s inst pre)] =
    let decoded = d inst in
    let pre_redacted = redact_system pre in

    let input_operand_values = (get_operands decoded.input_operands pre) in
    let output_operand_values = (s decoded input_operand_values) in
    let raw_post_state = (set_operands decoded.output_operands output_operand_values pre) in
    let post_state = decoding_execution_unit d s inst pre in

    let redacted_input_operand_values = (get_operands decoded.input_operands (redact_system pre)) in
    let redacted_output_operand_values = (s decoded redacted_input_operand_values) in
    let raw_post_state_redacted = (set_operands decoded.output_operands redacted_output_operand_values pre_redacted) in
    let post_state_redacted = decoding_execution_unit d s inst pre_redacted in

    lists_are_equivalent_to_their_redaction _ input_operand_values 0;
    get_operands_on_redacted_input_has_equivalent_output decoded.input_operands pre;
    assert(equiv_list input_operand_values redacted_input_operand_values);
    equivalent_memories_have_identical_any_blindedness input_operand_values redacted_input_operand_values;

    assert((any_value_is_blinded input_operand_values) = (any_value_is_blinded redacted_input_operand_values));

    assert(equiv_list input_operand_values redacted_input_operand_values);

    if not (any_value_is_blinded (input_operand_values)) then (
      assert(equiv_list input_operand_values redacted_input_operand_values);
      equivalent_unblinded_lists_are_equal input_operand_values redacted_input_operand_values;
      assert(input_operand_values = redacted_input_operand_values);
      assert(output_operand_values = redacted_output_operand_values);
      assert(post_state          = (set_operands decoded.output_operands output_operand_values pre));
      assert(post_state_redacted = (set_operands decoded.output_operands redacted_output_operand_values pre_redacted));

      systems_are_equivalent_to_their_redaction pre;
      equal_lists_are_equivalent _ output_operand_values redacted_output_operand_values;
      setting_equivalent_operand_values_on_equivalent_systems_yields_equivalent_systems decoded.output_operands output_operand_values redacted_output_operand_values pre pre_redacted;

      assert(equiv_system post_state post_state_redacted)
    ) else (

      assert(any_value_is_blinded input_operand_values);

      assert(post_state = set_operands decoded.output_operands (blind_all_values output_operand_values) pre);
      assert(post_state_redacted = set_operands decoded.output_operands (blind_all_values redacted_output_operand_values) pre_redacted);

      let blinded1 = blind_all_values output_operand_values in
      let blinded2 = blind_all_values redacted_output_operand_values in

      assert(FStar.List.length blinded1 = FStar.List.length blinded2);
      assert(all_values_are_blinded _ blinded1);
      assert(all_values_are_blinded _ blinded2);
      lists_of_blinded_values_of_equal_length_are_equivalent _ blinded1 blinded2;

      systems_are_equivalent_to_their_redaction pre;

      setting_equivalent_operand_values_on_equivalent_systems_yields_equivalent_systems decoded.output_operands blinded1 blinded2 pre pre_redacted
    )

let decoding_execution_unit_is_redacting_equivalent (d:decoder) (s:instruction_semantics):
  Lemma (ensures forall(pre:systemState) (inst:word).
                 (equiv_system (decoding_execution_unit d s inst pre)
                               (decoding_execution_unit d s inst (redact_system pre)))
                 \/ (trigger d s inst pre) )
    = ()

let each_decoding_execution_unit_is_safe (d:decoder) (s:instruction_semantics):
  Lemma (ensures is_safe (decoding_execution_unit d s))
  = decoding_execution_unit_is_redacting_equivalent d s;
    redacting_equivalent_execution_units_are_safe (decoding_execution_unit d s)
