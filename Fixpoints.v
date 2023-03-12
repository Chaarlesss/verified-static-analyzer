From Coq Require Import Relations.Relations.
From Coq Require Import Classes.RelationClasses.
From VSA Require Import Lattice.

Import SetNotations.

Class Increasing {A B: Type} (f: A -> B) `{Poset A} `{Poset B} := {
  increasing : forall x y, x ⊑ y -> f x ⊑ f y
}.

Definition image {A B : Type} (f : A -> B) (D : ℘ A) : ℘ B :=
  fun y => exists x, x ∈ D /\ f x = y.

Class ScottContinuous {A : Type} (f : A -> A) `{CompleteLattice A} : Prop := {
  scott_continuous : forall D, join (image f D) = f (join D)
}.

Definition PreFixpoints {A: Type} (f: A -> A) `{Increasing A A f}: ℘ A :=
  fun x => x ⊑ f x.

Definition PostFixpoints {A: Type} (f: A -> A) `{Increasing A A f}: ℘ A :=
  fun x => f x ⊑ x.

Definition Fixpoints {A: Type} (f: A -> A) `{Increasing A A f}: ℘ A :=
  fun x => f x = x.

Definition lfp_iff {A: Type} (f: A -> A) `{Increasing A A f} (u: A) :=
  LowerBound (Fixpoints f) u /\ u ∈ (Fixpoints f).

Definition glp_iff {A: Type} (f: A -> A) `{Increasing A A f} (u: A) :=
  UpperBound (Fixpoints f) u /\ u ∈ (Fixpoints f).

Section Tarski.

Context {A: Type} `{CompleteLattice A} (f: A -> A) {I: Increasing f}.

Definition lfp_tarski: A := meet (PostFixpoints f).

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
  lfp_iff f lfp_tarski.
Proof.
  split.
  - apply lfp_tarski_leastfixpoint.
  - apply lfp_tarski_fixpoint.
Qed.

End Tarski.


Section Kleene.
(* Class Extensive {A B: Type} (f: A -> B) `{Poset A} `{Poset B} := {
  increasing : forall x y, x ⊑ y -> f x ⊑ f y
}. *)

Context {A: Type} `{CompleteLattice A} (f: A -> A) {SC : ScottContinuous f}.

Lemma image_single_1:
  forall x, {{f x}} ⊆ image f {{x}}.
Proof.
  intros X x Hx.
  now exists X.
Qed.

Lemma image_single_2:
  forall x, image f {{x}} ⊆ {{f x}}.
Proof.
  now intros X x [? [-> ->]].
Qed.
Lemma subset_join:
  forall X Y : ℘ A,
    X ⊆ Y -> join X ⊑ join Y.
Proof.
  intros X Y Hincl. apply join_lub.
  intros x Hx%Hincl.
  now apply join_lub.
Qed.

Lemma eq_join:
  forall X Y : ℘ A,
    X ⊆ Y -> Y ⊆ X -> join X = join Y.
Proof.
  intros X Y HXY HYX.
  apply antisymmetry.
  - now apply subset_join.
  - now apply subset_join.
Qed.

Lemma join_bot:
  forall x, join ({{⊥}} ∪ x) = join x.
Proof.
  intros X.
  apply antisymmetry.
  - apply join_lub. intros x [-> | Hx].
    apply bottom_infimum.
    now apply join_lub.
  - apply join_lub. intros x Hx.
    apply join_lub. now right.
Qed.

Lemma join_singleton:
  forall x, join {{x}} = x.
Proof.
  intros X. apply antisymmetry.
  - apply join_lub. now intros x ->.
  - now apply join_lub.
Qed.

Lemma join_pair:
  forall x y, join {{x; y}} = x ⊔ y.
Proof.
  intros. apply antisymmetry.
  - apply join_lub.
    intros ? [-> | ->].
    apply join_sl_ub.
    apply join_sl_ub.
  - apply join_lub.
    intros z [<- | <-].
    apply join_lub. now left.
    apply join_lub. now right.
Qed.

Lemma join_max:
  forall x y, x ⊑ y -> x ⊔ y = y.
Proof.
  intros x y Hxy.
  apply antisymmetry.
  now apply join_sl_lub.
  apply join_sl_ub.
Qed.

Lemma f_incr:
  forall x y, x ⊑ y -> f x ⊑ f y.
Proof.
  intros x y Hxy.
  assert (H1 : f x ⊑ f x ⊔ f y) by apply join_sl_ub.
  pose proof (H2 := scott_continuous {{x; y}}).
  assert (H3 : x ⊔ y = y).
  apply antisymmetry.
  now apply join_sl_lub.
  apply join_sl_ub.
  rewrite join_pair in *.
  rewrite H3 in H2.
  etransitivity; eauto.
  transitivity (join (image f {{x; y}})); cycle 1.
  rewrite H2. reflexivity.
  apply subset_join. intros z [<- | <-].
  exists x. split; auto.
  exists y. split; auto.
Qed.

Instance scott_incr : Increasing f := {
  increasing := f_incr
}.

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
  intros y [ -> | [x [[n <-] <-]]].
  - now exists 0.
  - now exists (S n).
Qed.

Lemma iter_seq_image:
  iter_seq ⊆ {{⊥}} ∪ image f iter_seq.
Proof.
  intros x [[|n] <-].
  - now left.
  - right. exists (iter n). split; auto.
    now exists n.
Qed.

Definition lfp_kleene := join iter_seq.

Lemma lfp_kleene_fixpoint:
  lfp_kleene ∈ Fixpoints f.
Proof.
  unfold lfp_kleene.
  red. rewrite <- scott_continuous.
  rewrite <- join_bot.
  erewrite eq_join; eauto.
  - apply image_iter_seq.
  - apply iter_seq_image.
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
  apply join_lub.
  intros y [? <-].
  apply H0.
Qed.

Lemma lfp_in:
  lfp_kleene ∈ iter_seq.
Proof.
  unfold lfp_kleene.
  red.

End Kleene.

Definition ptjoin ()

Lemma gfp_2:
  join iter_seq ∈ iter_seq.
Proof.
  pose proof PointwiseFJoin.
  red. rewrite <- scott_continuous.
  rewrite <- join_bot.
  erewrite eq_join; eauto.
  - apply image_iter_seq.
  - apply iter_seq_image.
Qed.