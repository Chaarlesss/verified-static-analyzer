From Coq Require Import Program.Program.
From Coq Require Import Setoids.Setoid.
From Coq Require Import Classes.Morphisms.
From Coq Require Import Classes.RelationClasses.
From Coq Require Import Relations.
From Coq Require Import ssreflect ssrfun.
From HB Require Import structures.

HB.mixin Record Setoid_of_TYPE A := {
    equiv : relation A;
    equivE :> Equivalence equiv
}.
HB.structure Definition Setoid := { A of Setoid_of_TYPE A & }.

HB.mixin Record Poset_of_Setoid A of Setoid A := {
    ord : relation A;
    ordR : Reflexive ord;
    ordA : forall {x y}, ord x y -> ord y x -> equiv x y;
    ordT : Transitive ord;
    ordM : Proper (equiv ==> equiv ==> iff) ord
}.
HB.structure Definition Poset := { A of Poset_of_Setoid A & }.

Declare Scope vsa.
Open Scope vsa.

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

HB.instance
Definition Prop_Setoid :=
  Setoid_of_TYPE.Build Prop iff iff_equivalence.

Lemma implA: forall (x y: Prop), (impl x y) -> (impl y x) -> (iff x y).
Proof. firstorder. Qed.

Lemma implM: Proper (iff ==> iff ==> iff) impl.
Proof. firstorder. Qed.

HB.instance
Definition Prop_Poset :=
  Poset_of_Setoid.Build Prop impl impl_Reflexive implA impl_Transitive implM.

Class Morphism (X A: Setoid.type) : Type := {
  morphism : X -> A;
  morphism_proper :> Proper ((=) ==> (=)) morphism
}.

Coercion morphism : Morphism >-> Funclass.
Notation "X → A" := (Morphism X A) (at level 80, right associativity).
Notation "'λ' x ⇒ P" := ({| morphism := (fun x => P); morphism_proper := _ |})
                         (at level 200, x binder, right associativity).

Section Pointwise.

  Context (X: Setoid.type).

  Section Setoid.

  Context (A: Setoid.type).

  Definition Pointwise_equiv: relation (X → A) := fun f g => forall (x: X), f x = g x.

  Lemma Pointwise_equivE: Equivalence Pointwise_equiv.
  Proof.
    constructor.
      unfold Pointwise_equiv. unfold Reflexive.
      intros f x.
      assert (Equivalence (@equiv A)).
      Set Printing Implicit.
      Print equivE. apply equivE.
      reflexivity.

  End Setoid.

  Definition Pointwise_ord (X A: Poset.type): relation (X → A) := fun f g => forall (x: X), f x ⊑ g x.

End Pointwise.
