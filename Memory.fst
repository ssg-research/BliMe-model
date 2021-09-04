module Memory

open Value

type byte = b:int{0 >= b /\ b < 256}

type memoryState = list (maybeBlinded #byte)

let rec nth (m:memoryState) (n:nat) : maybeBlinded #byte = match m, n with
  | Nil,     _ -> Clear 0
  | hd :: tl, 0 -> hd
  | hd :: tl, n -> nth tl (n-1)

let _ = assert( forall (m:memoryState) (p:maybeBlinded #byte) (n:nat). nth m n == nth (p :: m) (n+1) )

let equal_memories_have_equal_values (a b: memoryState) (n:nat):
    Lemma (requires a = b)
          (ensures (nth a n) = (nth b n))
    = ()

let rec equivalent_memories_have_equivalent_values (a b: memoryState) (n: nat):
    Lemma (requires equiv_list a b)
          (ensures equiv (nth a n) (nth b n))
    = match n, a, b  with
      | 0, _, _ -> ()
      | _, hl :: tl, hr :: tr -> equivalent_memories_have_equivalent_values tl tr (n - 1)
      | _ -> ()
