From Coq Require Import Program.Program.
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

Notation "x ↾ p" := (exist _ x p) (at level 20) : vsa.

Module SetNotations.

  Notation "'℘' A" := (A -> Prop) (at level 0).
  Notation "x ∈ P" := (P x) (at level 19, only parsing).
  Notation "P ⊆ Q" := (forall x, x ∈ P -> x ∈ Q) (at level 20).
  Notation "P ∩ Q" := (fun x => x ∈ P /\ x ∈ Q) (at level 19).
  Notation "P ∪ Q" := (fun x => x ∈ P \/ x ∈ Q) (at level 19).
  Notation "¬ P" := (fun x => ~ (x ∈ P)) (at level 18).
  Notation "{{ x }}" := (fun y => y = x).
  Notation "{{ x ; y ; .. ; z }}" := (fun t => ( .. (t = x \/ t = y) .. \/ t = z)).
  Notation "∅" := (fun _ => False).

End SetNotations.

Import SetNotations.

Class SgOp A := sg_op: A -> A -> A.
Class SgSetOp A := sg_set_op: ℘ A -> A.
Class MonUnit A := mon_unit: A.

#[export]
Typeclasses Transparent SgOp SgSetOp MonUnit.

Infix "&" := sg_op (at level 50, left associativity) : vsa.
Notation "(&)" := sg_op (only parsing) : vsa.
Notation "( x &)" := (sg_op x) (only parsing) : vsa.
Notation "(& x )" := (fun y => y & x) (only parsing) : vsa.

Class Setoid (A: Type) `{E: Equiv A}: Prop :=
  setoid_equiv :> Equivalence (=).

Class Poset (A: Type) `{E: Equiv A} `{O: Ord A}: Prop := {
  poset_setoid :> Setoid A;
  poset_refl :> Reflexive (⊑);
  poset_antisym :> Antisymmetric A (=) (⊑);
  poset_trans :> Transitive (⊑);
  poset_proper :> Proper ((=) ==> (=) ==> iff) (⊑)
}.

Definition UpperBound {A: Type} `{O: Ord A} (S: ℘ A) (u: A) := forall x, x ∈ S -> x ⊑ u.
Definition LowerBound {A: Type} `{O: Ord A} (S: ℘ A) (u: A) := forall x, x ∈ S -> u ⊑ x.

Section Dual.

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
    pose proof (poset_setoid) as S.
    apply Build_Poset with S.
    - exact DualOrd_Reflexive.
    - exact DualOrd_Antisymmetric.
    - exact DualOrd_Transitive.
    - cbv. split; intro.
        rewrite <- H0. rewrite <- H. assumption.
        rewrite H0. rewrite H. assumption.
  Defined.

End Dual.

Section PropSetoid.

  #[global]
  Instance PropEquiv: Equiv Prop := iff.
  #[global]
  Instance PropOrd: Ord Prop := impl.

  #[program, global]
  Instance PropSetoid: Setoid Prop.

  #[program, global]
  Instance PropPoset: Poset Prop.
  Solve All Obligations with firstorder.

End PropSetoid.

Section Pointwise.

  Context (X A: Type) {E: Equiv A} {O: Ord A}.

  #[global]
  Instance PointwiseEquiv: Equiv (X -> A) :=
    fun f g => forall (x: X), f x = g x.

  #[global]
  Instance PointwiseOrd: Ord (X -> A) :=
    fun f g => forall (x: X), f x ⊑ g x.

  #[global]
  Instance PointwiseEquiv_Equivalence {St: Setoid A}: Equivalence PointwiseEquiv.
  Proof.
    constructor; repeat intro.
    - reflexivity.
    - symmetry. apply H.
    - transitivity (y x0). apply H. apply H0.
  Qed.

  #[global]
  Instance PointwiseOrd_Reflexive {P: Poset A}: Reflexive PointwiseOrd.
  Proof.
    intros f x. reflexivity.
  Qed.

  #[global]
  Instance PointwiseOrd_Antisymmetric {P: Poset A}: Antisymmetric (X -> A) PointwiseEquiv PointwiseOrd.
  Proof.
    intros f g H1 H2 x. now apply antisymmetry.
  Qed.

  #[global]
  Instance PointwiseOrd_Transitive {P: Poset A}: Transitive PointwiseOrd.
  Proof.
    intros f g h H1 H2 x. now transitivity (g x).
  Qed.

  #[program, global]
  Instance PointwisePoset {P: Poset A}: Poset (X -> A).
  Next Obligation.
    intros f f' H__f g g' H__g. split; intros H x; cbv in H__f, H__g.
    - rewrite <- H__f. rewrite <- H__g. apply H.
    - rewrite H__f. rewrite H__g. apply H.
  Qed.

End Pointwise.

Section Powerset.

  #[global]
  Instance PowersetEquiv {X: Type} : Equiv (℘ X) :=
    fun P Q => forall f, f ∈ P <-> f ∈ Q.

  #[global]
  Instance PowersetOrd {X: Type}: Ord (℘ X) :=
    fun P Q => P ⊆ Q.

  #[program, global]
  Instance PowersetSetoid {X: Type}: Setoid (℘ X).

  #[program, global]
  Instance PowersetPoset {X: Type}: Poset (℘ X).
  Solve All Obligations with firstorder.

End Powerset.

Section Projection.

  Context {A B: Type}.

  Lemma projected_setoid `{Setoid B} `{Equiv A} (f: A -> B)
    (eq_correct : forall x y, x = y <-> f x = f y) : Setoid A.
  Proof.
    constructor; repeat intro; apply eq_correct.
      reflexivity.
     symmetry. now apply eq_correct.
    transitivity (f y); now apply eq_correct.
  Qed.

  Lemma projected_poset `{Poset B} `{Equiv A} `{Ord A} (f: A -> B)
    (eq_correct : forall x y, x = y <-> f x = f y)
    (ord_correct : forall x y, x ⊑ y <-> f x ⊑ f y): Poset A.
  Proof.
    constructor 1 with (projected_setoid f eq_correct);
      repeat intro.
    - apply ord_correct. reflexivity.
    - apply eq_correct. apply antisymmetry; now apply ord_correct.
    - apply ord_correct. transitivity (f y); now apply ord_correct.
    - split; intro; apply ord_correct.
       rewrite eq_correct in H2, H3. rewrite <- H2. rewrite <- H3. now apply ord_correct.
      rewrite eq_correct in H2, H3. rewrite H2. rewrite H3. now apply ord_correct.
  Qed.

End Projection.

Definition SigEquiv {A: Type} `{Equiv A} (P: A -> Prop) : Equiv (sig P) := fun x y => `x = `y.
Definition SigOrd {A: Type} `{Ord A} (P: A -> Prop) : Ord (sig P) := fun x y => `x ⊑ `y.
Ltac simpl_sig_setoid :=
  match goal with
  | |- (@equiv _ (@SigEquiv _ ?e _) (?x↾_) (?y↾_)) => change (@equiv _ e x y)
  | |- (@ord _ (@SigOrd _ ?e _) (?x↾_) (?y↾_)) => change (@ord _ e x y)
  end.

#[global]
Hint Extern 10 (Equiv (sig _)) => apply @SigEquiv: typeclass_instances.
#[global]
Hint Extern 10 (Ord (sig _)) => apply @SigOrd: typeclass_instances.
#[global]
Hint Extern 4 (@equiv _ (SigEquiv _ _ _) (_↾_) (_↾_)) => simpl_sig_setoid: core.
#[global]
Hint Extern 4 (@ord _ (SigOrd _ _ _) (_↾_) (_↾_)) => simpl_sig_setoid: core.

#[global]
Instance SigSetoid {A: Type} `{Setoid A} (P : A -> Prop) : Setoid (sig P).
Proof. now apply (projected_setoid (@proj1_sig _ P)). Qed.

#[global]
Instance SigPoset {A: Type} `{Poset A} (P : A -> Prop) : Poset (sig P).
Proof. now apply (projected_poset (@proj1_sig _ P)). Qed.
