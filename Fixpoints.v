From Coq Require Import Relations.Relations.
From Coq Require Import Classes.RelationClasses.
From VSA Require Import Lattice.

Import SetNotations.

Class Increasing {A B: Type} (f: A -> B) `{Poset A} `{Poset B}: Prop :=
  increasing : forall x y, x ⊑ y -> f x ⊑ f y.

#[export]
Typeclasses Transparent Increasing.

Definition PreFixpoints {A: Type} (f: A -> A) `{Increasing A A f}: ℘ A :=
  fun x => x ⊑ f x.

Definition PostFixpoints {A: Type} (f: A -> A) `{Increasing A A f}: ℘ A :=
  fun x => f x ⊑ x.

Definition Fixpoints {A: Type} (f: A -> A) `{Increasing A A f}: ℘ A :=
  fun x => f x = x.

Definition lfp {A: Type} (f: A -> A) `{Increasing A A f} (u: A) :=
  LowerBound (Fixpoints f) u /\ u ∈ (Fixpoints f).

Definition glp {A: Type} (f: A -> A) `{Increasing A A f} (u: A) :=
  UpperBound (Fixpoints f) u /\ u ∈ (Fixpoints f).

Section Tarski.

  Context {A: Type} `{CompleteLattice A} (f: A -> A) {I: Increasing f}.

  Let lfp_tarski: A := meet (PostFixpoints f).

  Lemma lfp_tarski_fixpoint:
    f (lfp_tarski) = lfp_tarski.
  Proof.
    assert (f lfp_tarski ⊑ lfp_tarski).
    {
      apply meet_glb. intros x H__x.
      transitivity (f x); auto.
      apply increasing.
      apply meet_glb.
      assumption.
    }
    apply antisymmetry; auto.
    apply meet_glb. apply increasing. assumption.
  Qed.

  Lemma lfp_tarski_leastfixpoint:
    LowerBound (Fixpoints f) lfp_tarski.
  Proof.
    intros u H__u.
    apply meet_glb. unfold PostFixpoints. rewrite H__u. reflexivity.
  Qed.

  Theorem lfp_tarski_iff:
    lfp f lfp_tarski.
  Proof.
    split.
    - apply lfp_tarski_leastfixpoint.
    - apply lfp_tarski_fixpoint.
  Qed.

End Tarski.
