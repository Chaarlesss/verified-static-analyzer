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

(* TODO: move to another file *)
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
#[global]
Open Scope lattice.

Class Ord A := ord: relation A.
Class Equiv A := equiv: relation A.
#[global]
Typeclasses Transparent Ord Equiv.

Infix "⊑" := ord (at level 60, no associativity) : lattice.
Notation "(⊑)" := ord (only parsing) : lattice.
Notation "( X ⊑)" := (ord X) (only parsing) : lattice.
Notation "(⊑ X )" := (fun Y => Y ⊑ X) (only parsing) : lattice.

Infix "=" := equiv : type_scope.
Notation "(=)" := equiv (only parsing) : lattice.
Notation "( x =)" := (equiv x) (only parsing) : lattice.
Notation "(= x )" := (fun y => equiv y x) (only parsing) : lattice.

Infix "≡" := eq (at level 70, no associativity) : lattice.
Notation "(≡)" := eq (only parsing) : lattice.
Notation "( x ≡)" := (eq x) (only parsing) : lattice.
Notation "(≡ x )" := (fun y => eq y x) (only parsing) : lattice.

Class Setoid (A: Type) `{E: Equiv A}: Prop :=
  setoid_equiv :> Equivalence (=).

Class Poset (A: Type) `{E: Equiv A} {O: Ord A}: Prop := {
  poset_setoid :> Setoid A;
  poset_refl :> Reflexive (⊑);
  poset_antisym :> Antisymmetric A (=) (⊑);
  poset_trans :> Transitive (⊑)
}.

Definition UpperBound {A: Type} `{O: Ord A} (S: ℘ A) (u: A) := forall x, x ∈ S -> x ⊑ u.
Definition LowerBound {A: Type} `{O: Ord A} (S: ℘ A) (u: A) := forall x, x ∈ S -> u ⊑ x.

Class FMeet A := fmeet: A -> A -> A.
Class Meet A := meet: ℘ A -> A.
Class FJoin A := fjoin: A -> A -> A.
Class Join A := join: ℘ A -> A.
Class Top A := top: A.
Class Bottom A := bottom: A.

#[export]
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

Class JoinSemiLattice (A: Type) `{E: Equiv A} `{O: Ord A} `{J: FJoin A}: Prop := {
  join_sl_poset :> Poset A;
  join_sl_lub: forall x y u, x ⊑ u /\ y ⊑ u <-> (x ⊔ y) ⊑ u
}.

Class MeetSemiLattice (A: Type) `{E: Equiv A} `{O: Ord A} `{M: FMeet A}: Prop := {
  meet_sl_poset :> Poset A;
  meet_sl_glb: forall x y u, u ⊑ x /\ u ⊑ y <-> u ⊑ (x ⊓ y)
}.

Class Lattice (A: Type) `{E: Equiv A} `{O: Ord A} `{J: FJoin A} `{M: FMeet A}: Prop := {
  lattice_join_sl :> JoinSemiLattice A;
  lattice_meet_sl :> MeetSemiLattice A
}.

#[export]
Instance FJoinJoin (A: Type) `{J: Join A}: FJoin A := fun x y => join (PairSet x y).

#[export]
Instance FMeetMeet (A: Type) `{M: Meet A}: FMeet A := fun x y => meet (PairSet x y).

Class CompleteLattice (A: Type) `{E: Equiv A} `{O: Ord A} `{J: Join A} `{M: Meet A} `{T: Top A} `{B: Bottom A}: Prop := {
  complete_lattice_lattice :> Lattice A;
  join_lub: forall (S: ℘ A), UpperBound S (join S) /\ LowerBound (UpperBound S) (join S);
  meet_glb: forall (S: ℘ A), LowerBound S (meet S) /\ UpperBound (LowerBound S) (meet S);
  top_supremum: forall x, x ⊑ ⊤;
  bottom_infimum: forall x, ⊥ ⊑ x
}.

Section Dual.
#[local]
Set Printing Implicit.

Context (A: Type) {E: Equiv A} {O: Ord A} {J: Join A} {M: Meet A} {T: Top A} {B: Bottom A}.

Definition DualOrder: Ord A -> Ord A := (fun _ x y => ord y x).

Definition DualFJoin: FJoin A -> FMeet A := id.
Definition DualFMeet: FMeet A -> FJoin A := id.
Definition DualJoin: Join A -> Meet A := id.
Definition DualMeet: Meet A -> Join A := id.
Definition DualTop: Top A -> Bottom A := id.
Definition DualBottom: Bottom A -> Top A := id.

#[program, local]
Instance DualPoset {P: @Poset A E O}: @Poset A E (DualOrder O).
Next Obligation.
  reduce. reflexivity.
Defined.
Next Obligation.
  reduce. now apply antisymmetry.
Defined.
Next Obligation.
  reduce. now transitivity y.
Defined.

#[program, local]
Instance DualMeetSemiLattice {FM: FMeet A} {MSL: @MeetSemiLattice A E O FM}: @JoinSemiLattice A E (DualOrder O) (DualFMeet FM).
Next Obligation.
  cbv. apply meet_sl_glb.
Defined.

#[program, local]
Instance DualJoinSemiLattice {FJ: FJoin A} {JSL: @JoinSemiLattice A E O FJ}: @MeetSemiLattice A E (DualOrder O) (DualFJoin FJ).
Next Obligation.
  cbv. apply join_sl_lub.
Defined.

#[program, local]
Instance DualLattice {FJ: FJoin A} {FM: FMeet A} {L: @Lattice A E O FJ FM}: @Lattice A E (DualOrder O) (DualFMeet FM) (DualFJoin FJ).

Lemma DualJoinFJoin:
  @FMeetMeet A (DualJoin J) ≡ @DualFJoin (FJoinJoin A).
Proof.
  apply functional_extensionality. intros x.
  apply functional_extensionality. intros y.
  reflexivity.
Qed.

Lemma DualMeetFMeet:
  @FJoinJoin A (DualMeet M) ≡ @DualFMeet (FMeetMeet A).
Proof.
  apply functional_extensionality. intros x.
  apply functional_extensionality. intros y.
  reflexivity.
Qed.

#[program, local]
Instance DualCompleteLattice {L: CompleteLattice A}:
    @CompleteLattice A E (DualOrder O) (DualMeet M) (DualJoin J) (DualBottom B) (DualTop T).
Next Obligation.
  rewrite DualJoinFJoin. rewrite DualMeetFMeet. apply DualLattice.
Defined.
Next Obligation.
  cbv. apply meet_glb.
Defined.
Next Obligation.
  cbv. apply join_lub.
Defined.
Next Obligation.
  cbv. apply bottom_infimum.
Defined.
Next Obligation.
  cbv. apply top_supremum.
Defined.

End Dual.

(* TODO: write a tactic to automaticaly transform a context into its dual context *)
(* We should be able to add our own dual definitions (and a proof that they are indeed dual) *)
Section TestDual.

Context {A: Type}.

Lemma test_dual_join_sl_ub `{JoinSemiLattice A}:
  forall x y, x ⊑ (x ⊔ y) /\ y ⊑ (x ⊔ y).
Proof.
  intros. apply join_sl_lub. reflexivity.
Qed.

Local Set Printing Implicit.

Lemma test_dual_permut {B C} {f g: B -> B -> C}:
  f ≡ (fun x y => g y x) -> (fun x y => f y x) ≡ g.
Proof.
  intros H. repeat (apply functional_extensionality; intros).
  rewrite H. reflexivity.
Qed.

Lemma test_dual_meet_sl_lb `{MeetSemiLattice A}:
  forall x y, (x ⊓ y) ⊑ x /\ (x ⊓ y) ⊑ y.
Proof.
  (*
  remember (DualOrder A O0) as O1.
  remember (DualFMeet A M) as J.
  apply DualMeetSemiLattice in H.
  rewrite <- HeqO1 in *.
  rewrite <- HeqJ in *.
  unfold fmeet.
  clear M.
  subst.*)

  (** WORKING EXAMPLE **)
  apply DualMeetSemiLattice in H.

  remember (DualFMeet A M) as J.
  cbv in HeqJ. rewrite <- HeqJ.
  clear HeqJ. clear M.
  unfold fmeet. fold fjoin.

  remember (DualOrder A O0) as O1.
  cbv in HeqO1. rewrite <- (test_dual_permut HeqO1).
  clear HeqO1. clear O0.
  unfold ord. fold ord.

  apply test_dual_join_sl_ub.
Qed.

End TestDual.

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

Section Pointwise.

Context (X A: Type) {E: Equiv A} {O: Ord A} {J: Join A} {M: Meet A} {T: Top A} {B: Bottom A}.

Instance PointwiseEquiv: Equiv (X -> A) :=
  fun f g => forall (x: X), f x = g x.

Instance PointwiseOrd: Ord (X -> A) :=
   fun f g => forall (x: X), f x ⊑ g x.

Instance PointwiseFJoin {FJ: FJoin A}: FJoin (X -> A) :=
  fun f g (x: X) => f x ⊔ g x.

Instance PointwiseFMeet {FM: FMeet A}: FMeet (X -> A) :=
  fun f g (x: X) => f x ⊓ g x.

Instance PointwiseJoin: Join (X -> A) :=
  fun (S: ℘ (X -> A)) (x: X) => join (fun a => exists f, f ∈ S /\ a = f x).

Instance PointwiseMeet: Meet (X -> A) :=
  fun (S: ℘ (X -> A)) (x: X) => meet (fun a => exists f, f ∈ S /\ a = f x).

Instance PointwiseTop: Top (X -> A) :=
  fun _ => ⊤.

Instance PointwiseBottom: Bottom (X -> A) :=
  fun _ => ⊥.

Instance PointwiseEquiv_Equivalence {S: Setoid A}: Equivalence PointwiseEquiv.
Proof.
  apply Build_Equivalence; reduce.
  - reflexivity.
  - symmetry. apply H.
  - transitivity (y x0). apply H. apply H0.
Qed.

Instance PointwiseOrd_Reflexive {P: Poset A}: Reflexive PointwiseOrd.
Proof.
  intros f x. reflexivity.
Qed.

Instance PointwiseOrd_Antisymmetric {P: Poset A}: Antisymmetric (X -> A) PointwiseEquiv PointwiseOrd.
Proof.
  intros f g H1 H2 x. apply antisymmetry; auto.
Qed.

Instance PointwiseOrd_Transitive {P: Poset A}: Transitive PointwiseOrd.
Proof.
  intros f g h H1 H2 x. transitivity (g x). apply H1. apply H2.
Qed.

(* Our first soundness proof ! *)
(* However, we could avoid the functional extensionality using a different equivalence *)
Lemma PointwiseJoinFJoin {L: CompleteLattice A}:
  @FJoinJoin (X -> A) PointwiseJoin = @PointwiseFJoin (@FJoinJoin A J).
Proof.
  apply functional_extensionality. intros f.
  apply functional_extensionality. intros g.
  unfold FJoinJoin. unfold PointwiseFJoin. unfold join. unfold PointwiseJoin.
  apply antisymmetry.
  apply antisymmetry.
  - apply join_lub. intros z [h [[H__h | H__h] H__z]]; subst; apply join_sl_ub.
  - apply join_lub. intros z [H__z | H__z]; subst; apply join_lub; [ exists f | exists g ]; auto.
Qed.

Lemma PointwiseMeetFMeet {L: CompleteLattice A}:
  @FMeetMeet (X -> A) PointwiseMeet ≡ @PointwiseFMeet (FMeetMeet A).
Proof.
  apply functional_extensionality. intros f.
  apply functional_extensionality. intros g.
  apply functional_extensionality. intros x.
  apply antisymmetry.
  - apply meet_glb. intros z [H__z | H__z]; subst; apply meet_glb; [ exists f | exists g ]; auto.
  - apply meet_glb. intros z [h [[H__h | H__h] H__z]]; subst; apply meet_sl_lb.
Qed.

#[program]
Instance PointwisePoset `{Poset A} : Poset (X -> A).

#[program]
Instance PointwiseJoinSemiLattice `{FJoin A} `{JoinSemiLattice A}: JoinSemiLattice (X -> A).
Next Obligation.
  split.
  - intros [? ?] ?. apply join_sl_lub. auto.
  - intros H__join. split; intros x0; (transitivity (x x0 ⊔ y x0); [apply join_sl_ub | apply H__join]).
Defined.

#[program]
Instance PointwiseMeetSemiLattice `{FMeet A} `{MeetSemiLattice A}: MeetSemiLattice (X -> A).
Next Obligation.
  split.
  - intros [? ?] ?. apply meet_sl_glb. auto.
  - intros H__meet. split; intros x0; (transitivity (x x0 ⊓ y x0); [apply H__meet | apply meet_sl_lb]).
Qed.

#[program]
Instance PointwiseLattice `{Lattice A}: Lattice (X -> A).

#[program]
Instance PointwiseCompleteLattice `{CompleteLattice A}: CompleteLattice (X -> A).
Next Obligation.
  Local Set Printing Implicit.
  rewrite PointwiseJoinFJoin.
  rewrite PointwiseMeetFMeet.
  apply PointwiseLattice.
Defined.
Next Obligation.
  split.
  - intros f H__f x. apply join_lub. exists f. auto.
  - intros f H__f x. apply join_lub.
    intros a [g [H__g H__a]]; subst. apply H__f. assumption.
Qed.
Next Obligation.
  split.
  - intros f H__f x. apply meet_glb. exists f. auto.
  - intros f H__f x. apply meet_glb.
    intros a [g [H__g H__a]]; subst. apply H__f. assumption.
Qed.
Next Obligation.
  intros y. apply top_supremum.
Qed.
Next Obligation.
  intros y. apply bottom_infimum.
Qed.

End Pointwise.

Section Powerset.

Context (X: Type).

Instance PowersetOrd : Ord (℘ X) :=
  fun P Q => P ⊆ Q.

Instance PowersetFJoin : FJoin (℘ X) :=
  fun P Q => P ∪ Q.

Instance PowersetJoin : Join (℘ X) :=
  fun (S: ℘ (℘ X)) (x: X) => exists P, P ∈ S /\ x ∈ P.

Instance PowersetFMeet : FMeet (℘ X) :=
  fun P Q => P ∩ Q.

Instance PowersetMeet : Meet (℘ X) :=
  fun (S: ℘ (℘ X)) (x: X) => forall P, P ∈ S /\ x ∈ P.

Instance PowersetTop : Top (℘ X) :=
  fun _ => True.

Instance PowersetBottom : Bottom (℘ X) :=
  ∅.

Instance PowersetOrd_Reflexive : Reflexive PowersetOrd.
Proof.
  reduce. assumption.
Qed.

Instance PowsetOrd_Antisymmetric : Antisymmetric (℘ X) eq PowersetOrd.
Proof.
  (* Need to define custom equivalence *)
Admitted.

Instance PowersetOrd_Transitive: Transitive PowersetOrd.
Proof.
  reduce. auto.
Qed.

End Powerset.
