/// ******************
/// Multi-domain BliMe
/// ******************
///
/// Extends the analysis to multiple blindedness domains.
module Multi

open Value

/// The goal here is to show that we can transform a single-domain architecture
/// into a multi-domain one without sacrificing security.
///
/// ^^^^^^^^^^^
/// Definitions
/// ^^^^^^^^^^^
///
/// The ``multiBlinded`` type represents a type that may be blinded with any
/// of several blindedness domains.
type multiBlinded (#t:Type) =
  | MultiClear   : v:t            -> multiBlinded #t
  | MultiBlinded : (v:t) -> (d:int) -> multiBlinded #t

/// Convert a multiBlinded to a maybeBlinded by considering only blindedness
/// with respect to a single domain.
let for_domain (#t:Type) (d:int) (m: multiBlinded #t): maybeBlinded #t =
  match m with
  | MultiClear v     -> Clear v
  | MultiBlinded v d -> Blinded v
  | MultiBlinded v _ -> Clear v

/// Define a new notion of equivalence that applies to multi-domain
/// blinded values.
let domainwise_equiv (#t:eqtype) (d:int) (x y: multiBlinded #t) = equiv (for_domain d x) (for_domain d y)

let multi_bit_equiv  (#t:eqtype) (x y: multiBlinded #t)
    = match x, y with
       | MultiClear u, MultiClear v -> u = v
       | MultiBlinded u d1, MultiBlinded v d2 -> d1 = d2
       | _, _ -> false

let multi_bit_redaction (#t:eqtype) (x: multiBlinded #t) (v:t)
    = match x with
       | MultiBlinded _ d -> MultiBlinded v d
       | MultiClear v -> x

let multi_bit_unwrap (#t:eqtype) (x: multiBlinded #t)
    = match x with
       | MultiBlinded v _ -> v
       | MultiClear v -> v

/// Next, we prove the same lemmas as for single-bit blindedness.
///
/// Equivalence is an equivalence relation:
///
///  - **Reflexivity**
let equal_values_are_equivalent (t:eqtype) (lhs rhs:multiBlinded #t):
  Lemma (requires lhs = rhs)
        (ensures forall (d:int). domainwise_equiv d lhs rhs) =
  ()

///  - **Symmetry**
let equivalence_is_symmetric (t:eqtype) (d:int) (lhs rhs: multiBlinded #t):
    Lemma (requires domainwise_equiv d lhs rhs)
          (ensures  domainwise_equiv d rhs lhs)
    = ()

///  - **Transitivity**
let equivalence_is_transitive (t:eqtype) (d:int) (lhs mid rhs:multiBlinded #t):
    Lemma (requires (domainwise_equiv d lhs mid) /\ (domainwise_equiv d mid rhs))
          (ensures   domainwise_equiv d lhs rhs)
    = ()

/// Finally, we show that equivalence on non-blinded values is just the
/// normal equality relation.
let equivalent_clear_values_are_equal (t:eqtype) (x y:multiBlinded #t):
    Lemma (requires MultiClear? x /\ MultiClear? y /\ (exists (d:int). domainwise_equiv d x y))
          (ensures x = y)
    = ()

instance multi_bit_blinding (#inner:eqtype) : blinded_data_representation (multiBlinded #inner) = {
  inner = inner;
  equiv = multi_bit_equiv;
  is_blinded = (fun (x: multiBlinded #inner) -> MultiBlinded? x);
  redact = multi_bit_redaction;
  unwrap = multi_bit_unwrap;
  make_clear = MultiClear;
  properties =  ()
}

/// ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
/// Single- to multi-domain transformation
/// ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
///
/// Now we come up with a description of a multi-domain BliMe machine.  In the
/// single-domain case, an output is blinded if any inputs are blinded.  In the
/// multi-domain case, we look at all inputs for the computation, and there are
/// three possible cases:
///
///   1. No inputs are blinded, so no outputs are blinded
///
///   2. Inputs contain blinded data from one domain, so the output is blinded
///      with the same domain.
///
///   3. Inputs contain blinded data from multiple domains, so the computation
///      fails.
///
/// ### Security properties



