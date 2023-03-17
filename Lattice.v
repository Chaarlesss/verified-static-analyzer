From Coq Require Import Program.Basics.
From Coq Require Import Relations.Relations.
From Coq Require Import Setoids.Setoid.
From Coq Require Import Classes.Morphisms.
From Coq Require Import Classes.RelationClasses.
From VSA Require Import Basics.

Import SetNotations.

Class Meet A := meet: A -> A -> A.
Class Inf A := inf: ℘ A -> A.
Class Join A := join: A -> A -> A.
Class Sup A := sup: ℘ A -> A.
Class Top A := top: A.
Class Bottom A := bottom: A.

#[export]
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

Class JoinSemiLattice (A: Type) `{E: Equiv A} `{O: Ord A} `{J: Join A}: Prop := {
  join_sl_poset :> Poset A;
  join_lub: forall x y u, x ⊑ u /\ y ⊑ u <-> (x ⊔ y) ⊑ u
}.

Class MeetSemiLattice (A: Type) `{E: Equiv A} `{O: Ord A} `{M: Meet A}: Prop := {
  meet_sl_poset :> Poset A;
  meet_glb: forall x y u, u ⊑ x /\ u ⊑ y <-> u ⊑ (x ⊓ y)
}.

Class Lattice (A: Type) `{E: Equiv A} `{O: Ord A} `{J: Join A} `{M: Meet A}: Prop := {
  lattice_join_sl :> JoinSemiLattice A;
  lattice_meet_sl :> MeetSemiLattice A
}.

Class CompleteLattice (A: Type) `{E: Equiv A} `{O: Ord A} `{J: Join A} `{M: Meet A} `{S: Sup A} `{I: Inf A} `{T: Top A} `{B: Bottom A}: Prop := {
  complete_lattice_lattice :> Lattice A;
  sup_lub: forall (S: ℘ A) u, (sup S) ⊑ u <-> (forall x, x ∈ S -> x ⊑ u);
  inf_glb: forall (S: ℘ A) u, u ⊑ (inf S) <-> (forall x, x ∈ S -> u ⊑ x);
(*  join_lub: forall (S: ℘ A), UpperBound S (join S) /\ LowerBound (UpperBound S) (join S); *)
(*  meet_glb: forall (S: ℘ A), LowerBound S (meet S) /\ UpperBound (LowerBound S) (meet S); *)
  top_supremum: forall x, x ⊑ ⊤;
  bottom_infimum: forall x, ⊥ ⊑ x
}.

(* TODO: Compatibility lemma, spec, etc... *)

Section Dual.

  #[local]
  Set Printing Implicit.

  Context (A: Type) {E: Equiv A} {O: Ord A} {J: Join A} {M: Meet A} {S: Sup A} {I: Inf A} {T: Top A} {B: Bottom A}.

  Definition DualJoin: Meet A := J.
  Definition DualMeet: Join A := M.
  Definition DualSup: Inf A := S.
  Definition DualInf: Sup A := I.
  Definition DualTop: Bottom A := T.
  Definition DualBottom: Top A := B.

  Definition DualMeetSemiLattice {MSL: MeetSemiLattice A}: @JoinSemiLattice A E (DualOrd A) DualMeet.
  Proof.
    apply Build_JoinSemiLattice.
    - apply DualPoset. apply MSL.
    - cbv. apply meet_glb.
  Defined.

  Definition DualJoinSemiLattice {JSL: JoinSemiLattice A}: @MeetSemiLattice A E (DualOrd A) DualJoin.
  Proof.
    apply Build_MeetSemiLattice.
    - apply DualPoset. apply JSL.
    - cbv. apply join_lub.
  Defined.

  Definition DualLattice {L: Lattice A}: @Lattice A E (DualOrd A) DualMeet DualJoin.
  Proof.
    apply Build_Lattice.
    - apply DualMeetSemiLattice.
    - apply DualJoinSemiLattice.
  Defined.

  Definition DualCompleteLattice {L: CompleteLattice A}:
      @CompleteLattice A E (DualOrd A) DualMeet DualJoin DualInf DualSup DualBottom DualTop.
  Proof.
    apply Build_CompleteLattice.
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
    clear HeqJ. clear M.
    unfold meet. fold join.

    remember (DualOrd A) as O1.
    cbv in HeqO1. rewrite <- (test_dual_permut HeqO1).
    clear HeqO1. clear O0.
    unfold ord. fold ord.

    apply test_dual_join_ub.
  Qed.

End TestDual.
