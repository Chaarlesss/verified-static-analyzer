From Coq Require Import Program.Basics.
From Coq Require Import Relations.Relations.
From Coq Require Import Setoids.Setoid.
From Coq Require Import Classes.Morphisms.
From Coq Require Import Classes.RelationClasses.
From VSA Require Import Basics.
From VSA Require Import Functions.

Class Meet A `{Equiv A} := meet: A -> A -> A.
Class Inf A `{Equiv A} := inf: ℘ A -> A.
Class Join A `{Equiv A} := join: A -> A -> A.
Class Sup A `{Equiv A} := sup: ℘ A -> A.
Class Top A := top: A.
Class Bottom A := bottom: A.

#[global]
Typeclasses Transparent Meet Inf Join Sup Top Bottom.

Notation "⊤" := top : vsa.
Notation "⊥" := bottom : vsa.

Infix "⊓" := meet (at level 50, no associativity) : vsa.
Notation "(⊓)" := meet (only parsing) : vsa.
Notation "( X ⊓)" := (meet X) (only parsing) : vsa.
Notation "(⊓ X )" := (fun Y => Y ⊓ X) (only parsing) : vsa.

Infix "⊔" := join (at level 50, no associativity) : vsa.
Notation "(⊔)" := join (only parsing) : vsa.
Notation "( X ⊔)" := (join X) (only parsing) : vsa.
Notation "(⊔ X )" := (fun Y => Y ⊔ X) (only parsing) : vsa.

Class JoinSemiLattice (A: Type) `{!Equiv A} `{!Ord A} `{!Join A}: Prop := {
  join_sl_poset :> Poset A;
  join_lub: forall x y u, x ⊑ u /\ y ⊑ u <-> (x ⊔ y) ⊑ u
}.

Class MeetSemiLattice (A: Type) `{!Equiv A} `{!Ord A} `{!Meet A}: Prop := {
  meet_sl_poset :> Poset A;
  meet_glb: forall x y u, u ⊑ x /\ u ⊑ y <-> u ⊑ (x ⊓ y)
}.

Class Lattice (A: Type) `{!Equiv A} `{!Ord A} `{!Join A} `{!Meet A}: Prop := {
  lattice_join_sl :> JoinSemiLattice A;
  lattice_meet_sl :> MeetSemiLattice A
}.

Class CompleteLattice (A: Type) `{!Equiv A} `{!Ord A} `{!Join A} `{!Meet A} `{!Sup A} `{!Inf A} `{!Top A} `{!Bottom A}: Prop := {
  complete_lattice_lattice :> Lattice A;
  sup_lub: forall (S: ℘ A) u, (sup S) ⊑ u <-> (forall x, x ∈ S -> x ⊑ u);
  inf_glb: forall (S: ℘ A) u, u ⊑ (inf S) <-> (forall x, x ∈ S -> u ⊑ x);
  top_supremum: forall x, x ⊑ ⊤;
  bottom_infimum: forall x, ⊥ ⊑ x
}.


Section Preserve.

  Context {A B: Type} `{Equiv A} `{Equiv B} (f: A → B).

  Definition PreserveJoin `{!Join A} `{!Join B}: Prop := PreserveSgOp f (⊔) (⊔).
  Definition PreserveMeet `{!Meet A} `{!Meet B}: Prop := PreserveSgOp f (⊓) (⊓).
  Definition PreserveSup `{!Setoid B} {SA: Sup A} {SB: Sup B}: Prop := PreserveSgSetOp f SA SB.
  Definition PreserveInf `{!Setoid B} {IA: Inf A} {IB: Inf B}: Prop := PreserveSgSetOp f IA IB.
  Definition PreserveTop `{!Top A} `{!Top B}: Prop := f ⊤ = ⊤.
  Definition PreserveBottom `{!Bottom A} `{!Bottom B}: Prop := f ⊥ = ⊥.

End Preserve.


Section Stable.

  Context {A: Type} `{Equiv A} (P: ℘ A).

  Definition StableJoin `{!Join A}: Prop := StableSgOp P (⊔).
  Definition StableMeet `{!Meet A}: Prop := StableSgOp P (⊓).
  Definition StableSup {S: Sup A}: Prop := StableSgSetOp P S.
  Definition StableInf {I: Inf A}: Prop := StableSgSetOp P I.
  Definition StableTop `{!Top A}: Prop := P ⊤.
  Definition StableBottom `{!Bottom A}: Prop := P ⊥.

End Stable.


Section Dual.

  #[local]
  Set Printing Implicit.

  Context (A: Type) `{Setoid A} `{!Ord A} `{!Join A} `{!Meet A} {S: Sup A} {I: Inf A} `{!Top A} `{!Bottom A}.

  Definition DualJoin: Meet A := (⊔).
  Definition DualMeet: Join A := (⊓).
  Definition DualSup: Inf A := S.
  Definition DualInf: Sup A := I.
  Definition DualTop: Bottom A := (⊤).
  Definition DualBottom: Top A := (⊥).

  Definition DualMeetSemiLattice {MSL: MeetSemiLattice A}: @JoinSemiLattice A E (DualOrd A) DualMeet.
  Proof.
    constructor.
    - apply DualPoset. apply MSL.
    - cbv. apply meet_glb.
  Defined.

  Definition DualJoinSemiLattice {JSL: JoinSemiLattice A}: @MeetSemiLattice A E (DualOrd A) DualJoin.
  Proof.
    constructor.
    - apply DualPoset. apply JSL.
    - cbv. apply join_lub.
  Defined.

  Definition DualLattice {L: Lattice A}: @Lattice A E (DualOrd A) DualMeet DualJoin.
  Proof.
    constructor.
    - apply DualMeetSemiLattice.
    - apply DualJoinSemiLattice.
  Defined.

  Definition DualCompleteLattice {L: CompleteLattice A}:
      @CompleteLattice A E (DualOrd A) DualMeet DualJoin DualInf DualSup DualBottom DualTop.
  Proof.
    constructor.
    - apply DualLattice.
    - cbv. apply inf_glb.
    - cbv. apply sup_lub.
    - cbv. apply bottom_infimum.
    - cbv. apply top_supremum.
  Defined.

End Dual.

(* TODO: write a tactic to automaticaly transform a context into its dual context *)
(* We should be able to add our own dual definitions (and a proof that they are indeed dual) *)
Section TestDual.

  Context {A: Type}.
 
  Lemma test_dual_join_ub `{JoinSemiLattice A}:
    forall x y, x ⊑ (x ⊔ y) /\ y ⊑ (x ⊔ y).
  Proof.
    intros. apply join_lub. reflexivity.
  Qed.

  Local Set Printing Implicit.

  Lemma test_dual_permut {B C} {f g: B -> B -> C}:
    f ≡ (fun x y => g y x) -> (fun x y => f y x) ≡ g.
  Proof.
    intros H. rewrite H. reflexivity.
  Qed.

  Lemma test_dual_meet_lb `{MeetSemiLattice A}:
    forall x y, (x ⊓ y) ⊑ x /\ (x ⊓ y) ⊑ y.
  Proof.
    (** WORKING EXAMPLE **)
    apply DualMeetSemiLattice in H.

    remember (DualMeet A) as J.
    cbv in HeqJ. rewrite <- HeqJ.
    clear HeqJ. clear Meet0.
    unfold meet. fold join.

    remember (DualOrd A) as O1.
    cbv in HeqO1. rewrite <- (test_dual_permut HeqO1).
    clear HeqO1. clear Ord0.
    unfold ord. fold ord.

    apply test_dual_join_ub.
  Qed.

End TestDual.
