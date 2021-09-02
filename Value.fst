module Value

type maybeBlinded (#t:Type) =
   | Clear   : v:t -> maybeBlinded #t
   | Blinded : v:t -> maybeBlinded #t


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

let rec redact_list (#t:eqtype) (pre:list (maybeBlinded #t)) (d:t): list (maybeBlinded #t)
    = match pre with
      | Nil         -> Nil
      | head :: tail -> (redact head d) :: (redact_list tail d)

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
    = match lhs, rhs  with
      | hl :: tl, hr :: tr -> list_equivalence_is_symmetric t tl tr
      | _ -> ()


let rec list_equivalence_is_transitive (t:eqtype) (lhs mid rhs: list(maybeBlinded #t)):
    Lemma (requires (equiv_list lhs mid) /\ (equiv_list mid rhs))
          (ensures   equiv_list lhs rhs)
    = match lhs, mid, rhs  with
      | hl :: tl, hm :: tm, hr :: tr -> list_equivalence_is_transitive t tl tm tr
      | _ -> ()
