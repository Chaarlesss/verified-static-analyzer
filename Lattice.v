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

Section Join.

  Context {A: Type} `{JoinSemiLattice A}.
  
  Lemma join_ub:
    forall x y, x ⊑ (x ⊔ y) /\ y ⊑ (x ⊔ y).
  Proof.
    intros. apply join_lub. reflexivity.
  Qed.

  Lemma join_idempotent:
    forall x, x ⊔ x = x.
  Proof.
    intros x.
    apply antisymmetry.
    - apply join_lub. split; reflexivity.
    - apply join_ub.
  Qed.

  Lemma join_comm:
    forall x y, x ⊔ y = y ⊔ x.
  Proof.
    intros x y.
    apply antisymmetry; apply join_lub; split; apply join_ub.
  Qed.

  Lemma join_assoc:
    forall x y z, x ⊔ (y ⊔ z) = (x ⊔ y) ⊔ z.
  Proof.
    intros x y z.
    apply antisymmetry.
    - apply join_lub. split.
      * transitivity (x ⊔ y); apply join_ub.
      * apply join_lub. split.
        + transitivity (x ⊔ y); apply join_ub.
        + apply join_ub.
    - apply join_lub. split.
      * apply join_lub. split.
        + apply join_ub.
        + transitivity (y ⊔ z); apply join_ub.
      * transitivity (y ⊔ z); apply join_ub.
  Qed.

End Join.

Section Meet.

  Context {A: Type} `{MeetSemiLattice A}.
  
  Lemma meet_lb:
    forall x y, (x ⊓ y) ⊑ x /\ (x ⊓ y) ⊑ y.
  Admitted.

  Lemma meet_idempotent:
    forall x, x ⊓ x = x.
  Admitted.

  Lemma meet_comm:
    forall x y, x ⊓ y = y ⊓ x.
  Admitted.

  Lemma meet_assoc:
    forall x y z, x ⊓ (y ⊓ z) = (x ⊓ y) ⊓ z.
  Admitted.

End Meet.

Lemma join_meet_absortive {A: Type} `{Lattice A}:
  forall x y, (x ⊔ y) ⊓ x = x.
Proof.
  intros x y.
  apply antisymmetry.
  - apply meet_lb.
  - apply meet_glb. split.
    * apply join_ub.
    * reflexivity.
Qed.

Lemma meet_join_absortive {A: Type} `{Lattice A}:
  forall x y, (x ⊓ y) ⊔ x = x.
Admitted.

Section Sup.

  Context {A: Type} `{CompleteLattice A}.

  Lemma sup_ub:
    forall (S: ℘ A) x, x ∈ S -> x ⊑ sup S.
  Proof.
    intros S x H__x. destruct (sup_lub S (sup S)). firstorder.
  Qed.

End Sup.

Section Inf.

  Context {A: Type} `{CompleteLattice A}.

  Lemma inf_lb:
    forall (S: ℘ A) x, x ∈ S -> inf S ⊑ x.
  Admitted.

End Inf.

Section PropLattice.

  Instance PropJoin: Join Prop := or.
  Instance PropMeet: Meet Prop := and.
  Instance PropSup: Sup Prop := fun (S: ℘ Prop) => exists f, f ∈ S /\ f.
  Instance PropInf: Inf Prop := fun (S: ℘ Prop) => forall f, f ∈ S -> f.
  Instance PropTop: Top Prop := True.
  Instance PropBottom: Bottom Prop := False.

  #[program]
  Instance PropJoinSemiLattice: JoinSemiLattice Prop.
  Solve All Obligations with firstorder.

  #[program]
  Instance PropMeetSemiLattice: MeetSemiLattice Prop.
  Solve All Obligations with firstorder.

  #[program]
  Instance PropLattice: Lattice Prop.

  #[program]
  Instance PropCompleteLattice: CompleteLattice Prop.
  Solve All Obligations with firstorder.

End PropLattice.

Section Pointwise.

  Context (X A: Type) {E: Equiv A} {O: Ord A} {J: Join A} {M: Meet A} {S: Sup A} {I: Inf A} {T: Top A} {B: Bottom A}.

  #[export]
  Instance PointwiseJoin: Join (X -> A) :=
    fun f g (x: X) => f x ⊔ g x.

  #[export]
  Instance PointwiseMeet: Meet (X -> A) :=
    fun f g (x: X) => f x ⊓ g x.

  #[export]
  Instance PointwiseSup: Sup (X -> A) :=
    fun (S: ℘ (X -> A)) (x: X) => sup (fun a => exists f, f ∈ S /\ a = f x).

  #[export]
  Instance PointwiseInf: Inf (X -> A) :=
    fun (S: ℘ (X -> A)) (x: X) => inf (fun a => exists f, f ∈ S /\ a = f x).

  #[export]
  Instance PointwiseTop: Top (X -> A) :=
    fun _ => ⊤.

  #[export]
  Instance PointwiseBottom: Bottom (X -> A) :=
    fun _ => ⊥.

  #[program, export]
  Instance PointwiseJoinSemiLattice {JSL: JoinSemiLattice A}: JoinSemiLattice (X -> A).
  Next Obligation.
    split.
    - intros [? ?] ?. apply join_lub. auto.
    - intros H__join. split; intros x0; (transitivity (x x0 ⊔ y x0); [apply join_ub | apply H__join]).
  Qed.

  #[program, export]
  Instance PointwiseMeetSemiLattice {JSL: MeetSemiLattice A}: MeetSemiLattice (X -> A).
  Next Obligation.
    split.
    - intros [? ?] ?. apply meet_glb. auto.
    - intros H__meet. split; intros x0; (transitivity (x x0 ⊓ y x0); [apply H__meet | apply meet_lb]).
  Qed.

  #[program, export]
  Instance PointwiseLattice {L: Lattice A}: Lattice (X -> A).

  #[program, export]
  Instance PointwiseCompleteLattice {L: CompleteLattice A}: CompleteLattice (X -> A).
  Next Obligation.
    split.
    - intros H f H__f x. transitivity (sup S0 x); auto.
      apply sup_ub. exists f. split; auto. reflexivity.
    - intros H x. apply sup_lub. intros a [g [H__g H__a]]; subst. rewrite H__a. now apply H.
  Qed.
  Next Obligation.
    split.
    - intros H f H__f x. transitivity (inf S0 x); auto.
      apply inf_lb. exists f. split; auto. reflexivity.
    - intros H x. apply inf_glb. intros a [g [H__g H__a]]; subst. rewrite H__a. now apply H.
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

  #[export]
  Instance PowersetJoin : Join (℘ X) :=
    fun P Q => P ∪ Q.

  #[export]
  Instance PowersetMeet : Meet (℘ X) :=
    fun P Q => P ∩ Q.

  #[export]
  Instance PowersetSup : Sup (℘ X) :=
    fun (S: ℘ (℘ X)) (x: X) => exists P, P ∈ S /\ x ∈ P.

  #[export]
  Instance PowersetInf : Inf (℘ X) :=
    fun (S: ℘ (℘ X)) (x: X) => forall P, P ∈ S -> x ∈ P.

  #[export]
  Instance PowersetTop : Top (℘ X) :=
    fun _ => True.

  #[export]
  Instance PowersetBottom : Bottom (℘ X) :=
    ∅.

  #[program, export]
  Instance PowersetMeetSemiLattice: MeetSemiLattice (℘ X).
  Solve All Obligations with firstorder.

  #[program, export]
  Instance PowersetJoinSemiLattice: JoinSemiLattice (℘ X).
  Solve All Obligations with firstorder.

  #[program, export]
  Instance PowersetLattice: Lattice (℘ X).

  #[program, export]
  Instance PowersetCompleteLattice: CompleteLattice (℘ X).
  Solve All Obligations with firstorder.

End Powerset.
