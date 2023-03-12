From VSA Require Import Lattice.

Class Abstr A C := abstr : C -> A.
Class Concr C A := concr : A -> C.

#[export]
Typeclasses Transparent Abstr Concr.

Notation "'α' c" := (abstr c) (at level 20) : lattice.
Notation "('α')" := abstr (only parsing) : lattice.
Notation "'γ' c" := (concr c) (at level 20) : lattice.
Notation "('γ')" := concr (only parsing) : lattice.

Class GaloisConnection (A C: Type) `{OA: Poset A} `{OC: Poset C} (Abs: Abstr A C) (Concr: Concr C A) := {
  gc_poset_concr :> Poset C;
  gc_poset_abstr :> Poset A;
  gc_spec: forall (P: C) (Q: A), α P ⊑ Q <-> P ⊑ γ Q
}.
