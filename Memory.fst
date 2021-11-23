module Memory

open Value

type address = FStar.UInt64.t
type byte = FStar.UInt64.t

type memoryState = list (maybeBlinded #byte)

let rec nth (m:list (maybeBlinded #byte)) (n:address) : maybeBlinded #byte =
  match m, n with
    | Nil,     _   -> Blinded 0uL
    | hd :: tl, 0uL -> hd
    | hd :: tl, n   -> nth tl (FStar.UInt64.sub n 1uL)


let equal_memories_have_equal_values (a b: memoryState) (n:address):
    Lemma (requires a = b)
          (ensures (nth a n) = (nth b n))
    = ()

let rec equivalent_memories_have_equivalent_values (a b: memoryState) (n: address):
    Lemma (requires equiv_list a b)
          (ensures equiv (nth a n) (nth b n))
    = match n, a, b  with
      | 0uL, _, _ -> ()
      | _, hl :: tl, hr :: tr -> equivalent_memories_have_equivalent_values tl tr (FStar.UInt64.sub n 1uL)
      | _ -> ()


irreducible let trigger (a b: memoryState) (n:address) = True

let rec equivalent_memories_have_identical_blindedness_somewhere (a b: memoryState) (n:address):
  Lemma (requires equiv_list a b)
        (ensures Blinded? (nth a n) <==> Blinded? (nth b n))
        [SMTPat (trigger a b n)]=
  match n, a, b with
    | 0uL, _, _ -> ()
    | _, hl :: tl, hr :: tr -> equivalent_memories_have_identical_blindedness_somewhere tl tr (FStar.UInt64.sub n 1uL)
    | _ -> ()

