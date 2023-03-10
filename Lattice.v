Require Import Coq.Relations.Relations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.FunctionalExtensionality.

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

Section Sets.

  Record SetElt {A: Type} {S: A -> Prop}: Type := {
    elt: A;
    witness: elt ∈ S
  }.

  Definition PairSet {A: Type} (x y: A) : ℘ A := fun u => x = u \/ y = u.
  Definition PairSetElt {A: Type} (x y: A) := @SetElt _ (PairSet x y).
  Definition PairSetEltFirst {A : Type} (x y: A) : PairSetElt x y :=
     {| elt := x; witness := or_introl eq_refl |}.
  Definition PairSetEltSecond {A : Type} (x y: A) : PairSetElt x y :=
     {| elt := y; witness := or_intror eq_refl |}.

  Lemma PairSet_id {A: Type} (x y v: A):
    v ∈ (PairSet x y) <-> x = v \/ y = v.
  Proof.
    split; auto.
  Qed.

  Definition Transport {A: Type} {S T: ℘ A} (H : S ⊆ T): @SetElt _ S -> @SetElt _ T :=
    fun s => {| elt := elt s; witness := H (elt s) (witness s) |}.

End Sets.

Declare Scope lattice.
Global Open Scope lattice.

Class Ord A := ord: relation A.
Typeclasses Transparent Ord.

Infix "⊑" := ord (at level 60, no associativity) : lattice.
Notation "(⊑)" := ord (only parsing) : lattice.
Notation "( X ⊑)" := (ord X) (only parsing) : lattice.
Notation "(⊑ X )" := (fun Y => Y ⊑ X) (only parsing) : lattice.

Class Poset (A: Type) {O: Ord A}: Prop := {
  poset_refl :> Reflexive (⊑);
  poset_antisym :> Antisymmetric A eq (⊑);
  poset_trans :> Transitive (⊑)
}.

Definition UpperBound {A: Type} `{Ord A} (S: ℘ A) (u: A) := forall x, x ∈ S -> x ⊑ u.

Definition LowerBound {A: Type} `{Ord A} (S: ℘ A) (u: A) := forall x, x ∈ S -> u ⊑ x.

Class FMeet A := fmeet: A -> A -> A.
Class Meet A := meet: ℘ A -> A.
Class FJoin A := fjoin: A -> A -> A.
Class Join A := join: ℘ A -> A.
Class Top A := top: A.
Class Bottom A := bottom: A.

Typeclasses Transparent FMeet Meet FJoin Join Top Bottom.

Notation "⊤" := top : lattice.
Notation "⊥" := bottom : lattice.

Infix "⊓" := fmeet (at level 50, no associativity) : lattice.
Notation "(⊓)" := fmeet (only parsing) : lattice.
Notation "( X ⊓)" := (fmeet X) (only parsing) : lattice.
Notation "(⊓ X )" := (fun Y => Y ⊓ X) (only parsing) : lattice.

Infix "⊔" := fjoin (at level 50, no associativity) : lattice.
Notation "(⊔)" := fjoin (only parsing) : lattice.
Notation "( X ⊔)" := (fjoin X) (only parsing) : lattice.
Notation "(⊔ X )" := (fun Y => Y ⊔ X) (only parsing) : lattice.

Class JoinSemiLattice (A: Type) `{Ord A} `{FJoin A}: Prop := {
  join_sl_poset :> Poset A;
  join_sl_lub: forall x y u, x ⊑ u /\ y ⊑ u <-> (x ⊔ y) ⊑ u
}.

Class MeetSemiLattice (A: Type) `{Ord A} `{FMeet A}: Prop := {
  meet_sl_poset :> Poset A;
  meet_sl_glb: forall x y u, u ⊑ x /\ u ⊑ y <-> u ⊑ (x ⊓ y)
}.

Class Lattice (A: Type) `{Ord A} `{FJoin A} `{FMeet A}: Prop := {
  lattice_join_sl :> JoinSemiLattice A;
  lattice_meet_sl :> MeetSemiLattice A
}.

Instance FJoinJoin (A: Type) `{Join A}: FJoin A := fun x y => join (PairSet x y).

Instance FMeetMeet (A: Type) `{Meet A}: FMeet A := fun x y => meet (PairSet x y).

Class CompleteLattice (A: Type) `{Ord A} `{Join A} `{Meet A} `{Top A} `{Bottom A}: Prop := {
  complete_lattice_lattice :> Lattice A;
  meet_glb: forall (S: ℘ A), LowerBound S (meet S) /\ UpperBound (LowerBound S) (meet S);
  join_lub: forall (S: ℘ A), UpperBound S (join S) /\ LowerBound (UpperBound S) (join S);
  top_supremum: forall x, x ⊑ ⊤;
  bottom_infimum: forall x, ⊥ ⊑ x
}.

Section Join.

Context {A: Type} `{JoinSemiLattice A}.

Lemma join_sl_ub:
  forall x y, x ⊑ (x ⊔ y) /\ y ⊑ (x ⊔ y).
Proof.
  intros. apply join_sl_lub. reflexivity.
Qed.

Lemma join_sl_idempotent:
  forall x, x ⊔ x = x.
Proof.
  intros x.
  apply poset_antisym.
  - apply join_sl_lub. split; reflexivity.
  - apply join_sl_ub.
Qed.

Lemma join_sl_comm:
  forall x y, x ⊔ y = y ⊔ x.
Proof.
  intros x y.
  apply poset_antisym; apply join_sl_lub; split; apply join_sl_ub.
Qed.

Lemma join_sl_assoc:
  forall x y z, x ⊔ (y ⊔ z) = (x ⊔ y) ⊔ z.
Proof.
  intros x y z.
  apply poset_antisym.
  - apply join_sl_lub. split.
    * transitivity (x ⊔ y); apply join_sl_ub.
    * apply join_sl_lub. split.
      + transitivity (x ⊔ y); apply join_sl_ub.
      + apply join_sl_ub.
  - apply join_sl_lub. split.
    * apply join_sl_lub. split.
      + apply join_sl_ub.
      + transitivity (y ⊔ z); apply join_sl_ub.
    * transitivity (y ⊔ z); apply join_sl_ub.
Qed.

End Join.

Section Meet.

Context {A: Type} `{MeetSemiLattice A}.

Lemma meet_sl_lb:
  forall x y, (x ⊓ y) ⊑ x /\ (x ⊓ y) ⊑ y.
Admitted.

Lemma meet_sl_idempotent:
  forall x, x ⊓ x = x.
Admitted.

Lemma meet_sl_comm:
  forall x y, x ⊓ y = y ⊓ x.
Admitted.

Lemma meet_sl_assoc:
  forall x y z, x ⊓ (y ⊓ z) = (x ⊓ y) ⊓ z.
Admitted.

End Meet.

Lemma join_meet_sl_absortive {A: Type} `{Lattice A}:
  forall x y, (x ⊔ y) ⊓ x = x.
Proof.
  intros x y.
  apply antisymmetry.
  - apply meet_sl_lb.
  - apply meet_sl_glb. split.
    * apply join_sl_ub.
    * reflexivity.
Qed.

Lemma meet_join_absortive {A: Type} `{Lattice A}:
  forall x y, (x ⊓ y) ⊔ x = x.
Admitted.

Instance PointwiseOrd (X A: Type) `{Ord A} : Ord (X -> A) :=
   fun f g => forall (x : X), f x ⊑ g x.

Instance PointwiseFJoin (X A: Type) `{FJoin A} : FJoin (X -> A) :=
  fun f g (x : X) => f x ⊔ g x.

Instance PointwiseFMeet (X A: Type) `{FMeet A} : FMeet (X -> A) :=
  fun f g (x : X) => f x ⊓ g x.

Typeclasses Transparent PointwiseOrd PointwiseFJoin PointwiseFMeet.

Instance PointwiseOrd_Reflexive (X A: Type) `{Poset A}: Reflexive (PointwiseOrd X A).
Proof.
  reduce_goal. reflexivity.
Qed.

Instance PointwiseOrd_Antisymmetric (X A: Type) `{Poset A}: Antisymmetric (X -> A) eq (PointwiseOrd X A).
Proof.
  reduce_goal. apply functional_extensionality. intros z. apply poset_antisym; auto.
Qed.

Instance PointwiseOrd_Transitive (X A: Type) `{Poset A}: Transitive (PointwiseOrd X A).
Proof.
  reduce_goal. transitivity (y x0). apply H0. apply H1.
Qed.

Instance PointwisePoset (X A: Type) `{Poset A} : Poset (X -> A) := { }.

Program Instance PointwiseJoinSemiLattice (X A: Type) `{FJoin A} `{JoinSemiLattice A}: JoinSemiLattice (X -> A) := { }.
Next Obligation.
  split.
  - intros [? ?] ?. apply join_sl_lub. auto.
  - intros H__join. split; intros x0; (transitivity (x x0 ⊔ y x0); [apply join_sl_ub | apply H__join]).
Defined.

Program Instance PointwiseMeetSemiLattice (X A: Type) `{FMeet A} `{MeetSemiLattice A}: MeetSemiLattice (X -> A) := { }.
Next Obligation.
  split.
  - intros [? ?] ?. apply meet_sl_glb. auto.
  - intros H__meet. split; intros x0; (transitivity (x x0 ⊓ y x0); [apply H__meet | apply meet_sl_lb]).
Defined.

Instance PointwiseLattice (X A: Type) `{Lattice A}: Lattice (X -> A) := { }.
