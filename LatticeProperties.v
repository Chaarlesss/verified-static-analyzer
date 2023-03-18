From Coq Require Import Program.Program.
From Coq Require Import Relations.Relations.
From Coq Require Import Setoids.Setoid.
From Coq Require Import Classes.Morphisms.
From Coq Require Import Classes.RelationClasses.
From VSA Require Import Basics.
From VSA Require Import Lattice.
From VSA Require Import Functions.

Import SetNotations.

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

Section Projection.

  Context {A B: Type} `{CompleteLattice B} `{Equiv A} `{Ord A} `{Join A} `{Meet A} `{Sup A} `{Inf A} `{Top A} `{Bottom A}.

  Lemma projected_join_semi_lattice (f: A -> B)
    (eq_correct : forall x y, x = y <-> f x = f y)
    (ord_correct : forall x y, x ⊑ y <-> f x ⊑ f y)
    (join_correct : PreserveJoin f): JoinSemiLattice A.
  Proof.
    constructor.
     now apply (projected_poset f).
    intros x y u. split.
    - intros [H__x%ord_correct H__y%ord_correct]. apply ord_correct.
      rewrite join_correct. now apply join_lub.
    - intros H__u%ord_correct. rewrite join_correct in H__u.
      (* Using the right lemmas, can be shortened *)
      destruct (join_lub (f x) (f y) (f u)) as [_ H__fu].
      destruct (H__fu H__u). split; now apply ord_correct.
    Qed.

  Lemma projected_meet_semi_lattice (f: A -> B)
    (eq_correct : forall x y, x = y <-> f x = f y)
    (ord_correct : forall x y, x ⊑ y <-> f x ⊑ f y)
    (meet_correct : PreserveMeet f): MeetSemiLattice A.
  Admitted.

  Lemma projected_lattice (f: A -> B)
    (eq_correct : forall x y, x = y <-> f x = f y)
    (ord_correct : forall x y, x ⊑ y <-> f x ⊑ f y)
    (join_correct : PreserveJoin f)
    (meet_correct : PreserveMeet f): Lattice A.
  Proof.
    constructor.
    now apply (projected_join_semi_lattice f).
    now apply (projected_meet_semi_lattice f).
  Qed.

  Lemma projected_complete_lattice (f: A -> B)
    (eq_correct : forall x y, x = y <-> f x = f y)
    (ord_correct : forall x y, x ⊑ y <-> f x ⊑ f y)
    (join_correct : PreserveJoin f)
    (meet_correct : PreserveMeet f)
    (sup_correct : PreserveSup f)
    (inf_correct : PreserveInf f)
    (top_correct : PreserveTop f)
    (bottom_correct : PreserveBottom f): CompleteLattice A.
  Proof.
    constructor.
    - now apply (projected_lattice f).
    - split; intros; apply ord_correct.
      * transitivity (f (sup S)).
        (* TODO: lemma/tactic for this kind of trivial goal *)
         rewrite sup_correct. apply sup_ub. exists x. now split.
        now apply ord_correct.
      * rewrite sup_correct. apply sup_lub. intros y [x [H__x H__fx]]. rewrite H__fx.
        apply ord_correct. now apply H8.
    - split; intros; apply ord_correct.
      * transitivity (f (inf S)).
         now apply ord_correct.
        (* TODO: idem *)
        rewrite inf_correct. apply inf_lb. exists x. now split.
      * rewrite inf_correct. apply inf_glb. intros y [x [H__x H__fx]]. rewrite H__fx.
        apply ord_correct. now apply H8.
    - intros x. apply ord_correct. rewrite top_correct. apply top_supremum.
    - intros x. apply ord_correct. rewrite bottom_correct. apply bottom_infimum.
  Qed.

End Projection.
