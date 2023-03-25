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
#[global]
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

Class Setoid (A: Type) `{E: Equiv A}: Prop :=
  setoid_equiv :> Equivalence (=).

Record Sett (A: Type) `{Setoid A}: Type := {
    set_prop: A -> Prop;
    set_proper :> Proper ((=) ==> iff) (set_prop)
}.

Definition SetContains {A: Type} `{Setoid A} (x: A) (P: Sett A): Prop :=
  set_prop A P x.

#[program]
Definition SetSingleton {A: Type} `{Setoid A} (x: A): Sett A :=
  {| set_prop := fun y => y = x |}.
Next Obligation. solve_proper. Qed.

#[program]
Definition SetList {A: Type} `{Setoid A} (l: list A): Sett A :=
  let f := fun t => (fix f l' :=
        match l' with
        | nil => False
        | cons x q => t = x \/ (f q)
        end) in
  {| set_prop := fun x => f x l |}.
Next Obligation.
  split; induction l; auto; intros [|]; firstorder.
Qed.

#[program]
Definition SetEmpty {A: Type} `{Setoid A}: Sett A :=
  {| set_prop := fun _ => False |}.
Next Obligation. firstorder. Qed.

#[program]
Definition SetFull {A: Type} `{Setoid A}: Sett A :=
  {| set_prop := fun _ => True |}.
Next Obligation. firstorder. Qed.

Notation "'℘' A" := (Sett A) (at level 0).
Notation "x ∈ P" := (SetContains x P) (at level 19).
Notation "{{ x }}" := (SetSingleton x).
Notation "{{ x ; y ; .. ; z }}" := (SetList (cons x (cons y (.. (cons z nil) ..)))).
Notation "∅" := SetEmpty.

Lemma set_contains_singleton {A: Type} `{Setoid A} (x: A):
  forall u, u ∈ {{ x }} <-> u = x.
Proof. reflexivity. Qed.

Lemma set_contains_empty {A: Type} `{Setoid A}:
  forall u, u ∈ ∅ -> False.
Proof. contradiction. Qed.

Lemma set_contains_full {A: Type} `{Setoid A}:
  forall u, u ∈ SetFull.
Proof. firstorder. Qed.

Class SgOp A `{Setoid A} := sg_op: A -> A -> A.
Class SgSetOp A `{Setoid A} := sg_set_op: ℘ A -> A.
Class MonUnit A `{Setoid A} := mon_unit: A.

#[global]
Typeclasses Transparent SgOp SgSetOp MonUnit.

Infix "&" := sg_op (at level 50, left associativity) : vsa.
Notation "(&)" := sg_op (only parsing) : vsa.
Notation "( x &)" := (sg_op x) (only parsing) : vsa.
Notation "(& x )" := (fun y => y & x) (only parsing) : vsa.

Class Poset (A: Type) `{E: Equiv A} `{O: Ord A}: Prop := {
  poset_setoid :> Setoid A;
  poset_refl :> Reflexive (⊑);
  poset_antisym :> Antisymmetric A (=) (⊑);
  poset_trans :> Transitive (⊑);
  poset_proper :> Proper ((=) ==> (=) ==> iff) (⊑)
}.

Definition UpperBound {A: Type} `{Poset A} (S: ℘ A) (u: A) := forall x, x ∈ S -> x ⊑ u.
Definition LowerBound {A: Type} `{Poset A} (S: ℘ A) (u: A) := forall x, x ∈ S -> u ⊑ x.

Section Dual.

  #[local]
  Set Printing Implicit.

  Context (A: Type) {E: Equiv A} {O: Ord A}.

  Definition DualOrd: Ord A := flip (⊑).

  Hint Unfold DualOrd: core.

  Lemma DualOrd_Reflexive {P: Poset A}: Reflexive DualOrd.
  Proof. firstorder. Qed.

  Hint Unfold Antisymmetric: core.

  Lemma DualOrd_Antisymmetric {P: Poset A}: Antisymmetric A E DualOrd.
  Proof.
    autounfold. intros. now apply antisymmetry.
  Qed.

  Lemma DualOrd_Transitive {P: Poset A}: Transitive DualOrd.
  Proof. firstorder. Qed.

  Lemma DualPoset {P: Poset A}: @Poset A E DualOrd.
  Proof.
    pose proof (poset_setoid) as S.
    apply Build_Poset with S.
    - exact DualOrd_Reflexive.
    - exact DualOrd_Antisymmetric.
    - exact DualOrd_Transitive.
    - repeat intro. split; intro; cbv.
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

  #[program, global]
  Instance PointwiseEquiv_Equivalence {St: Setoid A}: Equivalence PointwiseEquiv.
  Solve All Obligations with firstorder.

  #[global]
  Instance PointwiseOrd_Reflexive {P: Poset A}: Reflexive PointwiseOrd.
  Proof. firstorder. Qed.

  #[global]
  Instance PointwiseOrd_Antisymmetric {P: Poset A}: Antisymmetric (X -> A) PointwiseEquiv PointwiseOrd.
  Proof.
    intros f g H1 H2 x. now apply antisymmetry.
  Qed.

  #[global]
  Instance PointwiseOrd_Transitive {P: Poset A}: Transitive PointwiseOrd.
  Proof. firstorder. Qed.

  #[program, global]
  Instance PointwisePoset {P: Poset A}: Poset (X -> A).
  Next Obligation.
    intros f f' H__f g g' H__g. split; intros H x; cbv in H__f, H__g.
    - rewrite <- H__f. rewrite <- H__g. apply H.
    - rewrite H__f. rewrite H__g. apply H.
  Qed.

End Pointwise.

Section Powerset.

  Context {X: Type} `{Setoid X}.

  #[global]
  Instance PowersetEquiv: Equiv (℘ X) :=
    fun P Q => forall f, f ∈ P <-> f ∈ Q.

  #[global]
  Instance PowersetOrd: Ord (℘ X) :=
    fun P Q => forall x, x ∈ P -> x ∈ Q.

  #[program, global]
  Instance PowersetSetoid: Setoid (℘ X).
  Solve All Obligations with firstorder.

  #[program, global]
  Instance PowersetPoset: Poset (℘ X).
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
