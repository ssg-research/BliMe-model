/// ****************
/// Blindable values
/// ****************
module Value

type maybeBlinded (#t:Type) =
   | Clear   : v:t -> maybeBlinded #t
   | Blinded : v:t -> maybeBlinded #t

let unwrap (#t:Type) (mb:maybeBlinded #t): t =
  match mb with
   | Clear v -> v
   | Blinded v -> v

val equiv (#t:eqtype)
    (lhs:maybeBlinded #t)
    (rhs:maybeBlinded #t)
    : r:prop{r <==> (    (Blinded? lhs /\ Blinded? rhs)
                      \/ (Clear?   lhs /\ Clear?   rhs  /\ Clear?.v lhs == Clear?.v rhs) )}

let equiv lhs rhs
    = match lhs, rhs with
      | Clear x, Clear y -> (x == y)
      | Blinded _, Blinded _ -> true
      | _ -> false


let equal_values_are_equivalent (t:eqtype) (lhs rhs:maybeBlinded #t):
  Lemma (requires lhs = rhs)
        (ensures equiv lhs rhs) =
  ()

let redact (#t:Type) (x: maybeBlinded #t) (d:t): maybeBlinded #t =
    match x with
    | Clear   v -> Clear v
    | Blinded t -> Blinded d

let _ = assert(forall (t:eqtype) (x y d: t). redact (Blinded x) d == redact (Blinded y) d)


let values_are_equivalent_to_their_redaction (t:eqtype) (x:maybeBlinded #t) (d:t):
    Lemma (ensures equiv x (redact x d))
    = ()

let equivalent_values_have_equal_redactions (t:eqtype) (x y:maybeBlinded #t) (d:t):
    Lemma (ensures equiv x y <==> redact x d = redact y d)
    = ()

let equivalence_is_transitive (t:eqtype) (lhs mid rhs:maybeBlinded #t):
    Lemma (requires (equiv lhs mid) /\ (equiv mid rhs))
          (ensures   equiv lhs rhs)
    = ()

let equivalence_is_symmetric (t:eqtype) (lhs rhs: maybeBlinded #t):
    Lemma (requires equiv lhs rhs)
          (ensures  equiv rhs lhs)
    = ()

let equivalent_clear_values_are_equal (t:eqtype) (x y:maybeBlinded #t):
    Lemma (requires Clear? x /\ Clear? y /\ equiv x y)
          (ensures x = y)
    = ()

/// .. fst::
///    :name: equiv_list
val equiv_list (#t:eqtype)
      (lhs:list (maybeBlinded #t))
      (rhs:list (maybeBlinded #t))
      : prop

let rec equiv_list (lhs:list maybeBlinded) (rhs: list maybeBlinded)
    = match lhs, rhs with
       | Nil,      Nil      -> true
       | Nil,      Cons _ _ -> false
       | Cons _ _, Nil      -> false
       | lh :: lt,  rh :: rt  -> (equiv lh rh) /\ (equiv_list lt rt)

let rec redact_list (#t:eqtype) (pre:list (maybeBlinded #t)) (d:t): r:(list (maybeBlinded #t)){FStar.List.length r = FStar.List.length pre}
    = match pre with
      | Nil         -> Nil
      | head :: tail -> (redact head d) :: (redact_list tail d)

let rec equivalent_lists_have_equal_lengths (#t:eqtype) (l1 l2:list (maybeBlinded #t))
  : Lemma (requires equiv_list l1 l2)
          (ensures FStar.List.length l1 = FStar.List.length l2)
  = match l1, l2 with
    | h1 :: t1, h2 :: t2 -> equivalent_lists_have_equal_lengths t1 t2
    | _ -> ()

let rec redaction_preserves_length (t:eqtype) (x:list(maybeBlinded #t)) (d:t)
  : Lemma (ensures FStar.List.length x = FStar.List.length (redact_list x d))
  = match x with
    | Nil -> ()
    | hd :: tl -> redaction_preserves_length t tl d

let rec equal_lists_are_equivalent (t:eqtype) (lhs rhs:list(maybeBlinded #t)):
    Lemma (requires lhs = rhs)
          (ensures equiv_list lhs rhs) =
    match lhs, rhs with
      | Nil, Nil -> ()
      | hl :: tl, hr :: tr -> (equal_values_are_equivalent t hl hr;
                            equal_lists_are_equivalent t tl tr)

let rec lists_are_equivalent_to_their_redaction (t:eqtype) (x: list(maybeBlinded #t)) (d:t)
    : Lemma (ensures equiv_list x (redact_list x d))
    = match x with
      | Nil -> ()
      | hd :: tl -> lists_are_equivalent_to_their_redaction t tl d


let rec equivalent_lists_have_equal_redactions (t:eqtype) (x y: list(maybeBlinded #t)) (d:t)
    : Lemma (ensures equiv_list x y <==> redact_list x d = redact_list y d)
    = match x, y with
       | Nil, Nil -> ()
       | Nil, Cons _ _ -> ()
       | Cons _ _, Nil -> ()
       | hl :: tl, hr :: tr -> equivalent_lists_have_equal_redactions t tl tr d

let rec list_equivalence_is_symmetric (t:eqtype) (lhs rhs: list(maybeBlinded #t)):
    Lemma (requires equiv_list lhs rhs)
          (ensures   equiv_list rhs lhs)
          [SMTPat (equiv_list lhs rhs)]
    = match lhs, rhs  with
      | hl :: tl, hr :: tr -> list_equivalence_is_symmetric t tl tr
      | _ -> ()


let rec list_equivalence_is_transitive (t:eqtype) (lhs mid rhs: list(maybeBlinded #t)):
    Lemma (requires (equiv_list lhs mid) /\ (equiv_list mid rhs))
          (ensures   equiv_list lhs rhs)
    = match lhs, mid, rhs  with
      | hl :: tl, hm :: tm, hr :: tr -> list_equivalence_is_transitive t tl tm tr
      | _ -> ()

let rec nth (#t:eqtype) (m:list (maybeBlinded #t)) (n:nat{n < FStar.List.length m}): maybeBlinded #t = match m, n with
    | hd :: tl, 0 -> hd
    | hd :: tl, n -> nth tl (n-1)

let rec redacted_lists_have_redacted_values (t:eqtype) (a: list (maybeBlinded #t)) (d:t) (n: nat{n < FStar.List.length a}):
  Lemma (ensures FStar.List.Tot.index (redact_list a d) n = redact (FStar.List.Tot.index a n) d)
        [SMTPat (FStar.List.Tot.index (redact_list a d) n)]
    = match n, a with
      | 0, _ -> ()
      | _, hl :: tl -> redacted_lists_have_redacted_values _ tl d (n - 1)
      | _ -> ()

let rec equivalent_lists_have_equivalent_values (t:eqtype) (a b: list (maybeBlinded #t)) (n: nat{n < FStar.List.length a && n < FStar.List.length b}):
    Lemma (requires equiv_list a b)
          (ensures equiv (FStar.List.Tot.index a n) (FStar.List.Tot.index b n))
    = match n, a, b  with
      | 0, _, _ -> ()
      | _, hl :: tl, hr :: tr -> equivalent_lists_have_equivalent_values _ tl tr (n - 1)
      | _ -> ()

let rec all_values_are_blinded (t:eqtype) (l: list (maybeBlinded #t)) =
  match l with
    | hd :: tl -> if Clear? hd then false else all_values_are_blinded t tl
    | _ -> true

let rec lists_of_blinded_values_of_equal_length_are_equivalent (t:eqtype) (a b: list (maybeBlinded #t)):
  Lemma (requires (FStar.List.length a = FStar.List.length b) /\ (all_values_are_blinded t a) /\ (all_values_are_blinded t b))
        (ensures equiv_list a b) =
  match a, b with
    | h1 :: t1, h2 :: t2 -> (
         lists_of_blinded_values_of_equal_length_are_equivalent t t1 t2
      )
    | _ -> ()
