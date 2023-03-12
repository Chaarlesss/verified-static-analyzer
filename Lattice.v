From Coq Require Import Program.Basics.
From Coq Require Import Relations.Relations.
From Coq Require Import Setoids.Setoid.
From Coq Require Import Classes.Morphisms.
From Coq Require Import Classes.RelationClasses.

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

Declare Scope lattice.
#[global]
Open Scope lattice.

Class Ord A := ord: relation A.
Class Equiv A := equiv: relation A.
#[export]
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
  poset_trans :> Transitive (⊑);
  poset_proper :> Proper ((=) ==> (=) ==> iff) (⊑)
}.

#[export]
Typeclasses Transparent Setoid.

Definition UpperBound {A: Type} `{O: Ord A} (S: ℘ A) (u: A) := forall x, x ∈ S -> x ⊑ u.
Definition LowerBound {A: Type} `{O: Ord A} (S: ℘ A) (u: A) := forall x, x ∈ S -> u ⊑ x.

Class Meet A := meet: A -> A -> A.
Class Inf A := inf: ℘ A -> A.
Class Join A := join: A -> A -> A.
Class Sup A := sup: ℘ A -> A.
Class Top A := top: A.
Class Bottom A := bottom: A.

#[export]
Typeclasses Transparent Meet Inf Join Sup Top Bottom.

Notation "⊤" := top : lattice.
Notation "⊥" := bottom : lattice.

Infix "⊓" := meet (at level 50, no associativity) : lattice.
Notation "(⊓)" := meet (only parsing) : lattice.
Notation "( X ⊓)" := (meet X) (only parsing) : lattice.
Notation "(⊓ X )" := (fun Y => Y ⊓ X) (only parsing) : lattice.

Infix "⊔" := join (at level 50, no associativity) : lattice.
Notation "(⊔)" := join (only parsing) : lattice.
Notation "( X ⊔)" := (join X) (only parsing) : lattice.
Notation "(⊔ X )" := (fun Y => Y ⊔ X) (only parsing) : lattice.

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

  Definition DualOrder: Ord A -> Ord A := (fun _ x y => ord y x).

  Definition DualJoin: Join A -> Meet A := id.
  Definition DualMeet: Meet A -> Join A := id.
  Definition DualSup: Sup A -> Inf A := id.
  Definition DualInf: Inf A -> Sup A := id.
  Definition DualTop: Top A -> Bottom A := id.
  Definition DualBottom: Bottom A -> Top A := id.

  #[program]
  Instance DualPoset {P: @Poset A E O}: @Poset A E (DualOrder O).
  Next Obligation.
    cbv. reflexivity.
  Qed.
  Next Obligation.
    cbv. intros. now apply antisymmetry.
  Qed.
  Next Obligation.
    cbv. intros. now transitivity y.
  Qed.
  Next Obligation.
    cbv. split; intro.
      rewrite <- H0. rewrite <- H. assumption.
      rewrite H0. rewrite H. assumption.
  Qed.

  #[program]
  Instance DualMeetSemiLattice {MSL: MeetSemiLattice A}: @JoinSemiLattice A E (DualOrder O) (DualMeet M).
  Next Obligation.
    cbv. apply meet_glb.
  Qed.

  #[program]
  Instance DualJoinSemiLattice {JSL: JoinSemiLattice A}: @MeetSemiLattice A E (DualOrder O) (DualJoin J).
  Next Obligation.
    cbv. apply join_lub.
  Qed.

  #[program]
  Instance DualLattice {L: Lattice A}: @Lattice A E (DualOrder O) (DualMeet M) (DualJoin J).

  #[program]
  Instance DualCompleteLattice {L: CompleteLattice A}:
      @CompleteLattice A E (DualOrder O) (DualMeet M) (DualJoin J) (DualInf I) (DualSup S) (DualBottom B) (DualTop T).
  Next Obligation.
    cbv. apply inf_glb.
  Qed.
  Next Obligation.
    cbv. apply sup_lub.
  Qed.
  Next Obligation.
    cbv. apply bottom_infimum.
  Qed.
  Next Obligation.
    cbv. apply top_supremum.
  Qed.

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

    remember (DualMeet A M) as J.
    cbv in HeqJ. rewrite <- HeqJ.
    clear HeqJ. clear M.
    unfold meet. fold join.

    remember (DualOrder A O0) as O1.
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

  Instance PropEquiv: Equiv Prop := iff.
  Instance PropOrd: Ord Prop := impl.
  Instance PropJoin: Join Prop := or.
  Instance PropMeet: Meet Prop := and.
  Instance PropSup: Sup Prop := fun (S: ℘ Prop) => exists f, f ∈ S /\ f.
  Instance PropInf: Inf Prop := fun (S: ℘ Prop) => forall f, f ∈ S -> f.
  Instance PropTop: Top Prop := True.
  Instance PropBottom: Bottom Prop := False.

  #[program]
  Instance PropSetoid: Setoid Prop.

  #[program]
  Instance PropPoset: Poset Prop.
  Solve All Obligations with firstorder.

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
  Instance PointwiseEquiv: Equiv (X -> A) :=
    fun f g => forall (x: X), f x = g x.

  #[export]
  Instance PointwiseOrd: Ord (X -> A) :=
    fun f g => forall (x: X), f x ⊑ g x.

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
  Instance PowersetEquiv : Equiv (℘ X) :=
    fun P Q => forall f, f ∈ P <-> f ∈ Q.

  #[export]
  Instance PowersetOrd : Ord (℘ X) :=
    fun P Q => P ⊆ Q.

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
  Instance PowersetPoset: Poset (℘ X).
  Solve All Obligations with firstorder.

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
