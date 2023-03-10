From Coq Require Import Relations.Relations.
From Coq Require Import Classes.RelationClasses.
From VSA Require Import Lattice.

Class Increasing (A B: Type) (f: A -> B) `{Poset A} `{Poset B} := {
  increasing : forall x y, x ⊑ y -> f x ⊑ f y
}.

Definition PreFixpoints {A: Type} (f: A -> A) `{Increasing A A f}: Subset A :=
  fun x => x ⊑ f x.

Definition PostFixpoints {A: Type} (f: A -> A) `{Increasing A A f}: Subset A :=
  fun x => f x ⊑ x.

Definition Fixpoints {A: Type} (f: A -> A) `{Increasing A A f}: Subset A :=
  fun x => f x = x.

Definition lfp {A: Type} (f: A -> A) `{Increasing A A f} (u: A) :=
  LowerBound (Fixpoints f) u /\ In (Fixpoints f) u.

Definition glp {A: Type} (f: A -> A) `{Increasing A A f} (u: A) :=
  UpperBound (Fixpoints f) u /\ In (Fixpoints f) u.

Section Tarski.

Context (A: Type) `{CompleteLattice A} (f: A -> A) {I: Increasing A A f}.

Definition lfp_expr: A := meet (PostFixpoints f).

Lemma lfp_fixpoint:
  f (lfp_expr) = lfp_expr.
Proof.
  assert (f lfp_expr ⊑ lfp_expr).
  {
    apply meet_glb. intros x H__x.
    transitivity (f x); auto.
    apply increasing.
    apply meet_glb.
    assumption.
  }
  apply antisymmetry; auto.
  apply meet_glb. unfold In. unfold PostFixpoints.
  apply increasing. assumption.
Qed.

Lemma lfp_leastfixpoint:
  LowerBound (Fixpoints f) lfp_expr.
Proof.
  intros u H__u.
  apply meet_glb. unfold In. unfold PostFixpoints. rewrite H__u. reflexivity.
Qed.

Theorem lfp_tarski:
  lfp f (meet (PostFixpoints f)).
Proof.
  split.
  - apply lfp_leastfixpoint.
  - apply lfp_fixpoint.
Qed.

End Tarski.
