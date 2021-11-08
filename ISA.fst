module ISA

open FStar.Math.Lib
open FStar.Mul

open Cpu
open Memory
open InstructionDecoder
open Value

let rec xor (a b:nat): nat =
  match a, b with
    | p, 0 -> p
    | 0, p -> p
    | _, _ -> (
         let next_a = (arithmetic_shift_right a 1) in
         let next_b = (arithmetic_shift_right b 1) in
         assert(next_a < a);
         assert(next_b < b);
         (if (a % 2) = (b % 2) then 0 else 1) + 2*xor next_a next_b
         )

let rec xor_each_element_is_own_inverse (x:nat):
  Lemma (ensures xor x x = 0)
        [SMTPat (xor x x)] =
    match x with
      | 0 -> ()
      | _ -> xor_each_element_is_own_inverse (arithmetic_shift_right x 1)

let rec land (a b:nat): nat =
  match a, b with
    | p, 0 -> 0
    | 0, p -> 0
    | _, _ -> (
         let next_a = (arithmetic_shift_right a 1) in
         let next_b = (arithmetic_shift_right b 1) in
         assert(next_a < a);
         assert(next_b < b);
         (if (a % 2 = 1) && (b % 2 = 1) then 1 else 0) + 2*land next_a next_b
         )

(* Instruction format:
 *
 *   opcode | out1 | in1 | in2 | imm
 *  63    61 60  56 55 51 50 46 45 0
 *)
let parse_opcode (inst:word) = (arithmetic_shift_right inst 61) % 8
let parse_out1 (inst:word): nat = (arithmetic_shift_right inst 56) % 32
let parse_in1 (inst:word): nat = (arithmetic_shift_right inst 51) % 32
let parse_in2 (inst:word): nat = (arithmetic_shift_right inst 45) % 32
let parse_imm (inst:word): nat = inst % ((pow2 46) - 1)

let sample_decoder (inst:word): decodedInstruction =

  let opcode = parse_opcode inst in
  let out1 = parse_out1 inst in
  let in1 = parse_in1 inst in
  let in2 = parse_in2 inst in
  match opcode with
  (* Store *)
    | 0 -> { opcode; input_operands = [ Register in1; Register in2 ]; output_operands = [] }
  (* Load *)
    | 1 -> { opcode; input_operands = [ Register in1; Register in2 ]; output_operands = [] }
  (* Branch *)
    | 2 -> { opcode; input_operands = [PC; Register in1; Register in2]; output_operands = [PC] }
  (* Arithmetic *)
    | 3 -> { opcode; input_operands = [ Register in1; Register in2 ]; output_operands = [ Register out1 ] }
    | 4 -> { opcode; input_operands = [ Register in1; Register in2 ]; output_operands = [ Register out1 ] }
    | 5 -> { opcode; input_operands = [ Register in1; Register in2 ]; output_operands = [ Register out1 ] }
    | 6 -> { opcode; input_operands = [ Register in1; Register in2 ]; output_operands = [ Register out1 ] }
    | 7 -> { opcode; input_operands = [ Register in1; Register in2 ]; output_operands = [ Register out1 ] }

let sample_decoded_instruction_length (inst:word):
  Lemma (ensures FStar.List.length (sample_decoder inst).input_operands =
                    (match (sample_decoder inst).opcode with
                     | 0 -> 2
                     | 1 -> 2
                     | 2 -> 3
                     | 3 -> 2
                     | 4 -> 2
                     | 5 -> 2
                     | 6 -> 2
                     | 7 -> 2
                     )
        )
        [SMTPat (sample_decoder inst)]=
  ()


val sample_semantics: instruction_semantics sample_decoder
let sample_semantics (di:decoder_output sample_decoder)
                     (pre:(list (maybeBlinded #word)){
                       (exists(s: systemState). pre = get_operands di.input_operands s) /\
                       FStar.List.length pre = FStar.List.length di.input_operands})
                     : instruction_result di =
  match di.opcode with
    (* Store *)
    | 0 -> let address = (FStar.List.Tot.index pre 0) in

    { register_writes = []; memory_ops = if Blinded? address then [] else (
      assert(FStar.List.length di.input_operands = 2);
      match (FStar.List.Tot.index di.input_operands 0), (FStar.List.Tot.index di.input_operands 1) with
        | Register d, Register s -> [Store (unwrap address) s]
        | _ -> []
      )}
    (* Load *)
    | 1 -> let address = (FStar.List.Tot.index pre 0) in
          { register_writes = [];
            memory_ops = if Blinded? address
                         then []
                         else match (FStar.List.Tot.index di.input_operands 0), (FStar.List.Tot.index di.input_operands 1) with
                               | Register d, Register s -> [Load (unwrap address) d]
                               | _ -> []}
    (* Branch *)
    | 2 -> ( let pc = FStar.List.Tot.index pre 0 in
            let a = FStar.List.Tot.index pre 1 in
            let b = FStar.List.Tot.index pre 2 in
            let ref: maybeBlinded #word = Clear #word 0 in

            { register_writes = [if a = ref then b else pc]; memory_ops = [] } )
    (* Add *)
    | 3 -> ( assert(FStar.List.length pre = 2);
            let a = FStar.List.Tot.index pre 0 in
            let b = FStar.List.Tot.index pre 1 in
            let result = (unwrap a) + (unwrap b) in
            let result = if any_value_is_blinded pre then Blinded result else Clear result in
           {
            register_writes = [result];
            memory_ops = [];
          })
    (* Sub *)
    | 4 -> ( assert(FStar.List.length pre = 2);
            let a = FStar.List.Tot.index pre 0 in
            let b = FStar.List.Tot.index pre 1 in
            let result = max 0 ((unwrap a) - (unwrap b)) in
            let result = if any_value_is_blinded pre then Blinded result else Clear result in
           {
            register_writes = [result];
            memory_ops = [];
          })
    (* MUL *)
    | 5 -> ( assert(FStar.List.length pre = 2);
            let a = FStar.List.Tot.index pre 0 in
            let b = FStar.List.Tot.index pre 1 in
            let result = (unwrap a) * (unwrap b) in
            let result = if (FStar.List.Tot.index di.input_operands 0) = (FStar.List.Tot.index di.input_operands 1) then
                            Clear 0
                         else if any_value_is_blinded pre then
                            Blinded result
                         else Clear result in
           {
            register_writes = [result];
            memory_ops = [];
          })
    (* AND *)
    | 6 -> ( assert(FStar.List.length pre = 2);
            let a: maybeBlinded #word = FStar.List.Tot.index pre 0 in
            let b: maybeBlinded #word = FStar.List.Tot.index pre 1 in
            let result: nat = land (unwrap a) (unwrap b) in
            let result = if (a = Clear #word 0) || (b = Clear #word 0) then
                            Clear 0
                         else if any_value_is_blinded pre then
                            Blinded result
                         else Clear result in
                         { register_writes = [result];
                           memory_ops = [];}
          )
    (* XOR *)
    | 7 -> ( assert(FStar.List.length pre = 2);
            let a = FStar.List.Tot.index pre 0 in
            let b = FStar.List.Tot.index pre 1 in
            let result: nat = xor (unwrap a) (unwrap b) in
            let result = if (FStar.List.Tot.index di.input_operands 0) = (FStar.List.Tot.index di.input_operands 1) then
                            Clear 0
                         else if any_value_is_blinded pre then
                            Blinded result
                         else Clear result in
                         { register_writes = [result];
                           memory_ops = [];}
          )

#set-options "--z3rlimit 10"
let sample_semantics_are_redacting_equivalent (inst:word)
                                      (pre:instruction_input (sample_decoder inst)):
  Lemma (ensures (equiv_result (sample_semantics (sample_decoder inst) pre)
                               (sample_semantics (sample_decoder inst)
                                                 (redacted_instruction_inputs_are_instruction_inputs (sample_decoder inst) pre)))) =
  ()

let add_instruction_works_correctly (inst:word)
                                    (pre:(list (maybeBlinded #word)){
                                      (exists(s: systemState). pre = get_operands (sample_decoder inst).input_operands s) /\
                                      FStar.List.length pre = FStar.List.length (sample_decoder inst).input_operands}):
    Lemma (requires parse_opcode inst = 3)
          (ensures  unwrap (FStar.List.Tot.hd (sample_semantics (sample_decoder inst) pre).register_writes) = (unwrap (FStar.List.Tot.index pre 0)) + (unwrap (FStar.List.Tot.index pre 1)) ) =
    ()


let xor_instruction_works_correctly (inst:word)
                                    (pre:(list (maybeBlinded #word)){
                                      (exists(s: systemState). pre = get_operands (sample_decoder inst).input_operands s) /\
                                      FStar.List.length pre = FStar.List.length (sample_decoder inst).input_operands}):
    Lemma (requires parse_opcode inst = 7)
          (ensures  unwrap (FStar.List.Tot.hd (sample_semantics (sample_decoder inst) pre).register_writes)
                    = xor (unwrap (FStar.List.Tot.index pre 0)) (unwrap (FStar.List.Tot.index pre 1)) ) =
    let di = sample_decoder inst in
    if (FStar.List.Tot.index di.input_operands 0) = (FStar.List.Tot.index di.input_operands 1) then
      assert(xor (unwrap (FStar.List.Tot.index pre 0)) (unwrap (FStar.List.Tot.index pre 1)) = 0)
    else
      ()
