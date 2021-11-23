module ISA

open FStar.Math.Lib
open FStar.Mul

open Cpu
open Memory
open InstructionDecoder
open Value

let v = FStar.UInt64.v

(* Instruction format:
 *
 *   opcode | out1 | in1 | in2 | imm
 *  63    61 60  56 55 51 50 46 45 0
 *)
let parse_opcode (inst:word) = (arithmetic_shift_right (v inst) 61) % 8
let parse_out1 (inst:word): nat = (arithmetic_shift_right (v inst) 56) % 32
let parse_in1 (inst:word): nat = (arithmetic_shift_right (v inst) 51) % 32
let parse_in2 (inst:word): nat = (arithmetic_shift_right (v inst) 45) % 32
let parse_imm (inst:word): nat = (v inst) % ((pow2 46) - 1)

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
        | Register d, Register s -> [Store (v (unwrap address)) s]
        | _ -> []
      )}
    (* Load *)
    | 1 -> let address = (FStar.List.Tot.index pre 0) in
          { register_writes = [];
            memory_ops = if Blinded? address
                         then []
                         else match (FStar.List.Tot.index di.input_operands 0), (FStar.List.Tot.index di.input_operands 1) with
                               | Register d, Register s -> [Load (v (unwrap address)) d]
                               | _ -> []}
    (* Branch *)
    | 2 -> ( let pc = FStar.List.Tot.index pre 0 in
            let a = FStar.List.Tot.index pre 1 in
            let b = FStar.List.Tot.index pre 2 in
            let ref: maybeBlinded #word = Clear #word 0uL in

            { register_writes = [if a = ref then b else pc]; memory_ops = [] } )
    (* Add *)
    | 3 -> ( assert(FStar.List.length pre = 2);
            let a: maybeBlinded #Cpu.word = FStar.List.Tot.index pre 0 in
            let b: maybeBlinded #Cpu.word = FStar.List.Tot.index pre 1 in
            let result: Cpu.word = (FStar.UInt64.add_mod (unwrap a) (unwrap b)) in
            let result = if any_value_is_blinded pre then Blinded result else Clear result in
           {
            register_writes = [result];
            memory_ops = [];
          })
    (* Sub *)
    | 4 -> ( assert(FStar.List.length pre = 2);
            let a = FStar.List.Tot.index pre 0 in
            let b = FStar.List.Tot.index pre 1 in
            let result: Cpu.word = (FStar.UInt64.sub_mod (unwrap a) (unwrap b)) in
            let result = if any_value_is_blinded pre then Blinded result else Clear result in
           {
            register_writes = [result];
            memory_ops = [];
          })
    (* MUL *)
    | 5 -> ( assert(FStar.List.length pre = 2);
            let a = FStar.List.Tot.index pre 0 in
            let b = FStar.List.Tot.index pre 1 in
            let result = (FStar.UInt64.mul_mod (unwrap a) (unwrap b)) in
            let result = if any_value_is_blinded pre then
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
            let result: Cpu.word = FStar.UInt64.logand (unwrap a) (unwrap b) in
            let result = if (a = Clear #word 0uL) || (b = Clear #word 0uL) then
                            Clear 0uL
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
            let result: Cpu.word = (FStar.UInt64.logxor (unwrap a) (unwrap b)) in
            let result = if (FStar.List.Tot.index di.input_operands 0) = (FStar.List.Tot.index di.input_operands 1) then
                            Clear 0uL
                         else if any_value_is_blinded pre then
                            Blinded result
                         else Clear result in
                         { register_writes = [result];
                           memory_ops = [];}
          )

irreducible let trigger (inst:word) (pre:instruction_input (sample_decoder inst)) = False

#set-options "--z3rlimit 1000"
let sample_semantics_are_redacting_equivalent_expanded (inst:word)
                                      (pre:instruction_input (sample_decoder inst)):
  Lemma (ensures (equiv_result (sample_semantics (sample_decoder inst) pre)
                               (sample_semantics (sample_decoder inst)
                                                 (redacted_instruction_inputs_are_instruction_inputs
                                                    (sample_decoder inst) pre)))
                 \/ trigger inst pre) =
  ()

let sample_semantics_are_redacting_equivalent (inst:word)
                                      (pre:instruction_input (sample_decoder inst)):
  Lemma (ensures is_redacting_equivalent_instruction_semantics_somewhere sample_decoder sample_semantics inst pre
                 \/ trigger inst pre) =
  ()

let sample_semantics_are_redacting_equivalent_everywhere ():
  Lemma (ensures is_redacting_equivalent_instruction_semantics_everywhere sample_decoder sample_semantics) =
  ()

let sample_semantics_are_safe ():
  Lemma (ensures is_safe (decoding_execution_unit sample_decoder sample_semantics)) =
    sample_semantics_are_redacting_equivalent_everywhere ();
    decoding_execution_unit_with_redacting_equivalent_instruction_semantics_is_redacting_equivalent sample_decoder sample_semantics;
    each_decoding_execution_unit_with_redacting_equivalent_instruction_semantics_is_safe sample_decoder sample_semantics

let sample_semantics_are_minimal (inst:word) (pre:instruction_input (sample_decoder inst)) (i:nat{i < FStar.List.length (sample_decoder inst).output_operands}):
  Lemma (requires Blinded? (FStar.List.Tot.index (sample_semantics (sample_decoder inst) pre).register_writes i))
        (ensures (let post = (sample_semantics (sample_decoder inst) pre).register_writes in
                  let post_i = FStar.List.Tot.index post i in
                          exists(y:instruction_input (sample_decoder inst)).
                              (equiv_list y pre)
                              /\  ~((FStar.List.Tot.index (sample_semantics (sample_decoder inst) y).register_writes i)
                                   == post_i))) =
        let di = sample_decoder inst in
        let post = (sample_semantics di pre).register_writes in
        match di.opcode with
          | 0 -> ()
          | 1 -> ()
          | 2 -> (
              assert(FStar.List.length post = 1);
              assert(i = 0);
              let post_i = FStar.List.Tot.index post i in
              assert(post_i = FStar.List.Tot.hd post);
              let pc = FStar.List.Tot.index pre 0 in
              let a = FStar.List.Tot.index pre 1 in
              let b = FStar.List.Tot.index pre 2 in
              assert((post_i = pc) \/ (post_i = b));
              assert(~(Blinded? pc));
              assert(Blinded? post_i ==> post_i = b);
              admit()
            )
          | 3 -> admit()
          | 4 -> admit()
          | 5 -> admit()
          | 6 -> admit()
          | 7 -> admit()


let add_instruction_works_correctly (inst:word)
                                    (pre:(list (maybeBlinded #word)){
                                      (exists(s: systemState). pre = get_operands (sample_decoder inst).input_operands s) /\
                                      FStar.List.length pre = FStar.List.length (sample_decoder inst).input_operands}):
    Lemma (requires parse_opcode inst = 3)
          (ensures  unwrap (FStar.List.Tot.hd (sample_semantics (sample_decoder inst) pre).register_writes)
                     = (FStar.UInt64.add_mod (unwrap (FStar.List.Tot.index pre 0)) (unwrap (FStar.List.Tot.index pre 1)))) =
    ()


let xor_with_self_yields_zero (a:Cpu.word):
  Lemma (ensures (FStar.UInt64.logxor a a) = 0uL) =
    let value: FStar.UInt.uint_t 64 = v a in
    FStar.UInt.logxor_self #64 value;
    assert(FStar.UInt.logxor #64 value value == 0)

let xor_instruction_works_correctly (inst:word)
                                    (pre:(list (maybeBlinded #word)){
                                      (exists(s: systemState). pre = get_operands (sample_decoder inst).input_operands s) /\
                                      FStar.List.length pre = FStar.List.length (sample_decoder inst).input_operands}):
    Lemma (requires parse_opcode inst = 7)
          (ensures  unwrap (FStar.List.Tot.hd (sample_semantics (sample_decoder inst) pre).register_writes)
                     = FStar.UInt64.logxor (unwrap (FStar.List.Tot.index pre 0)) (unwrap (FStar.List.Tot.index pre 1)) ) =
          let di = sample_decoder inst in
          let a = FStar.List.Tot.index pre 0 in
          let b = FStar.List.Tot.index pre 1 in
          let outputs = (sample_semantics (sample_decoder inst) pre).register_writes in
          if (FStar.List.Tot.index di.input_operands 0) = (FStar.List.Tot.index di.input_operands 1) then (
            assert(a == b);
            xor_with_self_yields_zero (unwrap a) )
          else if any_value_is_blinded pre then
            assert(outputs = [Blinded (FStar.UInt64.logxor (unwrap a) (unwrap b))])
          else
            assert(outputs = [Clear (FStar.UInt64.logxor (unwrap a) (unwrap b))])
