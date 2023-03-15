From Coq Require Import Program.Basics.
From Coq Require Import Relations.Relations.
From Coq Require Import Setoids.Setoid.
From Coq Require Import Classes.Morphisms.
From Coq Require Import Classes.RelationClasses.

Declare Scope vsa.
#[global]
Open Scope vsa.

Class Ord A := ord: relation A.
Class Equiv A := equiv: relation A.
#[export]
Typeclasses Transparent Ord Equiv.

Infix "⊑" := ord (at level 60, no associativity) : vsa.
Notation "(⊑)" := ord (only parsing) : vsa.
Notation "( X ⊑)" := (ord X) (only parsing) : vsa.
Notation "(⊑ X )" := (fun Y => Y ⊑ X) (only parsing) : vsa.

Infix "=" := equiv : type_scope.
Notation "(=)" := equiv (only parsing) : vsa.
Notation "( x =)" := (equiv x) (only parsing) : vsa.
Notation "(= x )" := (fun y => equiv y x) (only parsing) : vsa.

Infix "≡" := eq (at level 70, no associativity) : vsa.
Notation "(≡)" := eq (only parsing) : vsa.
Notation "( x ≡)" := (eq x) (only parsing) : vsa.
Notation "(≡ x )" := (fun y => eq y x) (only parsing) : vsa.

Class Setoid (A: Type) `{E: Equiv A}: Prop :=
  setoid_equiv :> Equivalence (=).

Class Poset (A: Type) `{E: Equiv A} {O: Ord A}: Prop := {
  poset_setoid :> Setoid A;
  poset_refl :> Reflexive (⊑);
  poset_antisym :> Antisymmetric A (=) (⊑);
  poset_trans :> Transitive (⊑);
  poset_proper :> Proper ((=) ==> (=) ==> iff) (⊑)
}.

Module SetNotations.

  Notation "'℘' A" := (A -> Prop) (at level 0).
  Notation "x ∈ P" := (P x) (at level 19, only parsing).
  Notation "P ⊆ Q" := (forall x, x ∈ P -> x ∈ Q) (at level 20).
  Notation "P ∩ Q" := (fun x => x ∈ P /\ x ∈ Q) (at level 19).
  Notation "P ∪ Q" := (fun x => x ∈ P \/ x ∈ Q) (at level 19).
  Notation "{{ x }}" := (fun y => y = x).
  Notation "{{ x ; y ; .. ; z }}" := (fun t => ( .. (t = x \/ t = y) .. \/ t = z)).
  Notation "∅" := (fun _ => False).

End SetNotations.

Import SetNotations.

Definition UpperBound {A: Type} `{O: Ord A} (S: ℘ A) (u: A) := forall x, x ∈ S -> x ⊑ u.
Definition LowerBound {A: Type} `{O: Ord A} (S: ℘ A) (u: A) := forall x, x ∈ S -> u ⊑ x.

Section DualSetoid.

  #[local]
  Set Printing Implicit.

  Context (A: Type) {E: Equiv A} {O: Ord A}.

  Definition DualOrd: Ord A := flip (⊑).

  Lemma DualOrd_Reflexive {P: Poset A}: Reflexive DualOrd.
  Proof.
    cbv. reflexivity.
  Qed.

  Lemma DualOrd_Antisymmetric {P: Poset A}: Antisymmetric A E DualOrd.
  Proof.
    cbv. intros. now apply antisymmetry.
  Qed.

  Lemma DualOrd_Transitive {P: Poset A}: Transitive DualOrd.
  Proof.
    cbv. intros. now transitivity y.
  Qed.

  Lemma DualPoset {P: Poset A}: @Poset A E DualOrd.
  Proof.
    assert (@Setoid A E) as S. { apply poset_setoid. }
    apply Build_Poset with S.
    - exact DualOrd_Reflexive.
    - exact DualOrd_Antisymmetric.
    - exact DualOrd_Transitive.
    - cbv. split; intro.
        rewrite <- H0. rewrite <- H. assumption.
        rewrite H0. rewrite H. assumption.
  Defined.

End DualSetoid.

Section PropSetoid.

  #[export]
  Instance PropEquiv: Equiv Prop := iff.
  #[export]
  Instance PropOrd: Ord Prop := impl.

  #[program, export]
  Instance PropSetoid: Setoid Prop.

  #[program, export]
  Instance PropPoset: Poset Prop.
  Solve All Obligations with firstorder.

End PropSetoid.

Section PointwiseSetoid.

  Context (X A: Type) {E: Equiv A} {O: Ord A}.

  #[export]
  Instance PointwiseEquiv: Equiv (X -> A) :=
    fun f g => forall (x: X), f x = g x.

  #[export]
  Instance PointwiseOrd: Ord (X -> A) :=
    fun f g => forall (x: X), f x ⊑ g x.

  #[export]
  Instance PointwiseEquiv_Equivalence {St: Setoid A}: Equivalence PointwiseEquiv.
  Proof.
    apply Build_Equivalence; reduce.
    - reflexivity.
    - symmetry. apply H.
    - transitivity (y x0). apply H. apply H0.
  Qed.

  #[export]
  Instance PointwiseOrd_Reflexive {P: Poset A}: Reflexive PointwiseOrd.
  Proof.
    intros f x. reflexivity.
  Qed.

  #[export]
  Instance PointwiseOrd_Antisymmetric {P: Poset A}: Antisymmetric (X -> A) PointwiseEquiv PointwiseOrd.
  Proof.
    intros f g H1 H2 x. apply antisymmetry; auto.
  Qed.

  #[export]
  Instance PointwiseOrd_Transitive {P: Poset A}: Transitive PointwiseOrd.
  Proof.
    intros f g h H1 H2 x. transitivity (g x). apply H1. apply H2.
  Qed.

  #[program, export]
  Instance PointwisePoset {P: Poset A}: Poset (X -> A).
  Next Obligation.
    intros f f' H__f g g' H__g. split; intros H.
    - intros x. cbv in H__f, H__g. rewrite <- H__f. rewrite <- H__g. apply H.
    - intros x. cbv in H__f, H__g. rewrite H__f. rewrite H__g. apply H.
  Qed.

End PointwiseSetoid.

Section PowersetSetoid.

  Context (X: Type).

  #[export]
  Instance PowersetEquiv : Equiv (℘ X) :=
    fun P Q => forall f, f ∈ P <-> f ∈ Q.

  #[export]
  Instance PowersetOrd : Ord (℘ X) :=
    fun P Q => P ⊆ Q.

  #[program, export]
  Instance PowersetPoset: Poset (℘ X).
  Solve All Obligations with firstorder.

End PowersetSetoid.
