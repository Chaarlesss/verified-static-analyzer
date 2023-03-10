From VSA Require Import Lattice.

Class Abstraction A C := abstraction : C -> A.
Class Concretization C A := concretization : A -> C.

Typeclasses Transparent Abstraction Concretization.

Notation "'α' c" := (abstraction c) (at level 20) : lattice.
Notation "('α')" := abstraction (only parsing) : lattice.
Notation "'γ' c" := (concretization c) (at level 20) : lattice.
Notation "('γ')" := concretization (only parsing) : lattice.

Class GaloisConnection (A C: Type) {OA: Ord A} {OC: Ord C} (Abs: Abstraction A C) (Concr: Concretization C A) := {
  gc_poset_concrete :> Poset C;
  gc_poset_abstract :> Poset A;
  gc: forall (P: C) (Q: A), α P ⊑ Q <-> P ⊑ γ Q
}.
