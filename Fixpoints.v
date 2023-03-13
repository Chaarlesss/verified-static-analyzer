From Coq Require Import Relations.Relations.
From Coq Require Import Classes.RelationClasses.
From Coq Require Import Setoids.Setoid.
From Coq Require Import Classes.Morphisms.
From Coq Require Import Relations.Relations.
From VSA Require Import Lattice.
From VSA Require Import Functions.

Import SetNotations.

Section ScottContinuity.

Class ScottContinuous {A : Type} (f : A -> A) `{CompleteLattice A} : Prop := {
  scott_continuous : forall D, sup (image f D) = f (sup D)
}.

#[program, export]
Instance scott_continuous_increasing {A : Type} {f : A -> A} `{ScottContinuous _ f} {P : Proper ((=) ==> (=)) f} : Increasing f.
Next Obligation.
  pose proof (Hxy := scott_continuous {{x; y}}).
  rewrite sup_pair, join_is_right in Hxy by auto.
  rewrite <- Hxy.
  apply sup_ub. exists x.
  split. now left. auto.
  reflexivity.
Defined.

End ScottContinuity.

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

  Definition lfp_tarski: A := inf (PostFixpoints f).

  Lemma lfp_tarski_fixpoint:
    f (lfp_tarski) = lfp_tarski.
  Proof.
    assert (f lfp_tarski ⊑ lfp_tarski).
    {
      apply inf_glb. intros x H__x.
      transitivity (f x); auto.
      apply increasing.
      apply inf_lb.
      assumption.
    }
    apply antisymmetry; auto.
    apply inf_lb. apply increasing. assumption.
  Qed.

  Lemma lfp_tarski_leastfixpoint:
    LowerBound (Fixpoints f) lfp_tarski.
  Proof.
    intros u H__u.
    apply inf_lb. unfold PostFixpoints. rewrite H__u. reflexivity.
  Qed.

  Theorem lfp_tarski_iff:
    lfp f lfp_tarski.
  Proof.
    split.
    - apply lfp_tarski_leastfixpoint.
    - apply lfp_tarski_fixpoint.
  Qed.

End Tarski.


Section Kleene.

Context {A: Type} `{CompleteLattice A} (f: A -> A) {SC : ScottContinuous f}.
Context {P : Proper ((=) ==> (=)) f}.

Lemma image_singleton:
  forall x, image f {{x}} = {{f x}}.
Proof.
  intros X. split.
  - now intros [x [-> ->]].
  - intros Hx. now exists X.
Qed.

Fixpoint iter (n : nat) :=
  match n with
  | 0 => ⊥
  | S n => f (iter n)
  end.

Definition iter_seq : ℘ A :=
  fun x => exists n, iter n = x.

Lemma iter_incr:
  forall n, iter n ⊑ iter (S n).
Proof.
  induction n; simpl.
  - apply bottom_infimum.
  - apply increasing, IHn.
Qed.

Lemma image_iter_seq:
  {{⊥}} ∪ image f iter_seq ⊆ iter_seq.
Proof.
  intros y [Hy | [x [[n <-] Hx]]]. 
  + now exists 0.
  + now exists (S n).
Qed.

Lemma iter_seq_image:
  iter_seq ⊆ {{⊥}} ∪ image f iter_seq.
Proof.
  intros x [[|n] Hx].
  - now left.
  - right. exists (iter n).
    split; try easy.
    now exists n.
Qed.

Lemma iter_seq_image_eq:
  iter_seq = {{⊥}} ∪ image f iter_seq.
Proof.
  split; intros.
  now apply iter_seq_image.
  now apply image_iter_seq.
Qed.

Definition lfp_kleene := sup iter_seq.

Lemma lfp_kleene_fixpoint:
  lfp_kleene ∈ Fixpoints f.
Proof.
  unfold lfp_kleene. red.
  rewrite <- scott_continuous.
  rewrite iter_seq_image_eq at 2.
  now rewrite <- sup_union_bot.
Qed.

Lemma lfp_kleene_leastfixpoint:
  LowerBound (Fixpoints f) (lfp_kleene).
Proof.
  unfold lfp_kleene.
  intros x Hx.
  assert (forall i, iter i ⊑ x).
  { induction i.
    apply bottom_infimum.
    apply increasing in IHi.
    etransitivity; eauto.
    rewrite Hx. reflexivity.
  }
  apply sup_lub.
  intros y [? <-].
  apply H0.
Qed.

End Kleene.