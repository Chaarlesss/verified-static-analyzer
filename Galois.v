From Coq Require Import Relations.Relations.
From Coq Require Import Classes.RelationClasses.
From VSA Require Import Basics.
From VSA Require Import Lattice.
From VSA Require Import Functions.

Import SetNotations.

Class Abstr C A := alpha : C -> A.
Class Concr C A := gamma : A -> C.

#[export]
Typeclasses Transparent Abstr Concr.

Notation "'α' c" := (alpha c) (at level 20) : vsa.
Notation "'(α)'" := alpha (only parsing) : vsa.
Notation "'γ' c" := (gamma c) (at level 20) : vsa.
Notation "'(γ)'" := gamma (only parsing) : vsa.

Class GaloisConnection (C A: Type) `{PC: Poset C} `{PA: Poset A} (Ab: Abstr C A) (Co: Concr C A): Prop := {
  gc_poset_concr :> Poset C;
  gc_poset_abstr :> Poset A;
  gc_spec: forall (P: C) (Q: A), α P ⊑ Q <-> P ⊑ γ Q
}.

Class GaloisRetraction (C A: Type) `{PA: Poset A} `{PC: Poset C} (Ab: Abstr C A) (Co: Concr C A): Prop := {
  gr_gc :> GaloisConnection C A Ab Co;
  gr_abstr_surjective :> Surjective Ab
}.

Class GaloisIsomorphism (C A: Type) `{PA: Poset A} `{PC: Poset C} (Ab: Abstr C A) (Co: Concr C A): Prop := {
  gi_gc :> GaloisConnection C A Ab Co;
  gi_abstr_bijective :> Bijective Ab
}.

Section Properties.

  Context {C A: Type} {Ab: Abstr C A} {Co: Concr C A} `{Poset C} `{Poset A} {GC: GaloisConnection C A Ab Co}.

  Lemma alpha_increasing:
    Increasing (α).
  Proof.
    intros P P' H__P. apply gc_spec.
    transitivity P'; auto. now apply gc_spec.
  Qed.

  Lemma gamma_increasing:
    Increasing (γ).
  Admitted.
  (* By duality *)

  Lemma alpha_gamma_comp:
    forall x, α (γ (α x)) = α x.
  Proof.
    intros x.
    apply antisymmetry.
      now apply gc_spec.
    apply alpha_increasing.
    apply gc_spec.
    reflexivity.
  Qed.

  Lemma gamma_alpha_comp:
    forall y, γ (α (γ y)) = γ y.
  Admitted.

  Lemma gamma_alpha_extensive:
    forall x, x ⊑ γ (α x).
  Proof.
    intros x. now apply gc_spec.
  Qed.

  Lemma alpha_gamma_reductive:
    forall y, α (γ y) ⊑ y.
  Admitted.

End Properties.
