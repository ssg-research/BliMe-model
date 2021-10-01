module Memory

open Value

type byte = nat

type memoryState = list (maybeBlinded #byte)

let rec nth (m:list (maybeBlinded #byte)) (n:nat) : maybeBlinded #byte = match m, n with
  | Nil,     _ -> Blinded 0
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


irreducible let trigger (a b: memoryState) (n:nat) = True

let rec equivalent_memories_have_identical_blindedness_somewhere (a b: memoryState) (n:nat):
  Lemma (requires equiv_list a b)
        (ensures Blinded? (nth a n) <==> Blinded? (nth b n))
        [SMTPat (trigger a b n)]=
  match n, a, b with
    | 0, _, _ -> ()
    | _, hl :: tl, hr :: tr -> equivalent_memories_have_identical_blindedness_somewhere tl tr (n-1)
    | _ -> ()

