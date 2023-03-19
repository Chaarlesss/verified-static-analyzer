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

  Lemma join_increasing:
    forall x y z u, x ⊑ y -> z ⊑ u -> x ⊔ z ⊑ y ⊔ u.
  Proof.
    intros x y z u H__ord1 H__ord2. apply join_lub; split.
     transitivity y. assumption. now apply join_ub.
    transitivity u. assumption. now apply join_ub.
  Qed.

   Lemma join_increasing_l:
    forall x y z, x ⊑ y -> x ⊔ z ⊑ y ⊔ z.
  Proof.
    intros x y z H__orq. now apply join_increasing.
  Qed.

  Lemma join_increasing_r:
    forall x y z, x ⊑ y -> z ⊔ x ⊑ z ⊔ y.
  Proof.
    intros x y z H__orq. now apply join_increasing.
  Qed.

  #[global]
  Instance: Proper ((=) ==> (=) ==> (=)) (⊔).
  Proof.
    intros x y H1 x' y' H2. apply antisymmetry; apply join_lub; split.
    - rewrite H1. now apply join_ub.
    - rewrite H2. now apply join_ub.
    - rewrite <- H1. now apply join_ub.
    - rewrite <- H2. now apply join_ub.
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

  Lemma meet_increasing:
    forall x y z u, x ⊑ y -> z ⊑ u -> x ⊓ z ⊑ y ⊓ u.
  Proof.
    intros x y z u H__ord1 H__ord2. apply meet_glb; split.
      transitivity x. now apply meet_lb. assumption.
    transitivity z. now apply meet_lb. assumption.
  Qed.

  Lemma meet_increasing_l:
    forall x y z, x ⊑ y -> x ⊓ z ⊑ y ⊓ z.
  Proof.
    intros x y z H__orq. now apply meet_increasing.
  Qed.

  Lemma meet_increasing_r:
    forall x y z, x ⊑ y -> z ⊓ x ⊑ z ⊓ y.
  Proof.
    intros x y z H__orq. now apply meet_increasing.
  Qed.

  #[global]
  Instance: Proper ((=) ==> (=) ==> (=)) (⊓).
  Proof.
    intros x y H1 x' y' H2. apply antisymmetry; apply meet_glb; split.
    - rewrite <- H1. now apply meet_lb.
    - rewrite <- H2. now apply meet_lb.
    - rewrite H1. now apply meet_lb.
    - rewrite H2. now apply meet_lb.
  Qed.

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

  Lemma sup_increasing:
    Increasing (sup).
  Proof.
    intros P Q H__S. apply sup_lub. intros x H__x%H__S. now apply sup_ub.
  Qed.

End Sup.

Section Inf.

  Context {A: Type} `{CompleteLattice A}.

  Lemma inf_lb:
    forall (S: ℘ A) x, x ∈ S -> inf S ⊑ x.
  Admitted.

  (* Lemma inf_decreasing *)

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

  #[program, global]
  Instance PowersetCompleteLattice: CompleteLattice (℘ X).
  Solve All Obligations with firstorder.

End Powerset.

Section Projection.

  Context {A B: Type} `{Equiv A} `{Ord A} `{Join A} `{Meet A} `{Sup A} `{Inf A} `{Top A} `{Bottom A}.

  Lemma projected_join_semi_lattice `{JoinSemiLattice B} (f: A -> B)
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

  Lemma projected_meet_semi_lattice `{MeetSemiLattice B} (f: A -> B)
    (eq_correct : forall x y, x = y <-> f x = f y)
    (ord_correct : forall x y, x ⊑ y <-> f x ⊑ f y)
    (meet_correct : PreserveMeet f): MeetSemiLattice A.
  Proof.
    constructor.
     now apply (projected_poset f).
    intros x y u. split.
    - intros [H__x%ord_correct H__y%ord_correct]. apply ord_correct.
      rewrite meet_correct. now apply meet_glb.
    - intros H__u%ord_correct. rewrite meet_correct in H__u.
      (* Using the right lemmas, can be shortened *)
      destruct (meet_glb (f x) (f y) (f u)) as [_ H__fu].
      destruct (H__fu H__u). split; now apply ord_correct.
    Qed.

  Lemma projected_lattice `{Lattice B} (f: A -> B)
    (eq_correct : forall x y, x = y <-> f x = f y)
    (ord_correct : forall x y, x ⊑ y <-> f x ⊑ f y)
    (join_correct : PreserveJoin f)
    (meet_correct : PreserveMeet f): Lattice A.
  Proof.
    constructor.
    now apply (projected_join_semi_lattice f).
    now apply (projected_meet_semi_lattice f).
  Qed.

  Lemma projected_complete_lattice `{CompleteLattice B} (f: A -> B)
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

Definition SigJoin {A: Type} `{Join A} (P: A -> Prop) (join_correct: StableJoin P): Join (sig P) :=
  fun x y => (`x ⊔ `y) ↾ (join_correct _ _ (proj2_sig x) (proj2_sig y)).

Definition SigMeet {A: Type} `{Meet A} (P: A -> Prop) (meet_correct: StableMeet P): Meet (sig P) :=
  fun x y => (`x ⊓ `y) ↾ (meet_correct _ _ (proj2_sig x) (proj2_sig y)).

#[program]
Definition SigSup {A: Type} `{Sup A} (P: A -> Prop) (sup_correct: StableSup P): Sup (sig P) :=
  fun (S: ℘ ({ x: A | P x })) => (sup (image (@proj1_sig _ P) S)) ↾ _.
Next Obligation.
  apply sup_correct. intros x [[x' H__x'] [_ H__x]]. subst. now apply H__x'.
Defined.

#[program]
Definition SigInf {A: Type} `{Inf A} (P: A -> Prop) (inf_correct: StableInf P): Inf (sig P) :=
  fun (S: ℘ ({ x: A | P x })) => (inf (image (@proj1_sig _ P) S)) ↾ _.
Next Obligation.
  apply inf_correct. intros x [[x' H__x'] [_ H__x]]. subst. now apply H__x'.
Defined.

Definition SigTop {A: Type} `{Top A} (P: A -> Prop) (top_correct: StableTop P): Top (sig P) :=
  ⊤ ↾ top_correct.

Definition SigBottom {A: Type} `{Bottom A} (P: A -> Prop) (bottom_correct: StableBottom P): Bottom (sig P) :=
  ⊤ ↾ bottom_correct.

#[global]
Hint Extern 10 (Join (sig _)) => now apply SigJoin: typeclass_instances.
#[global]
Hint Extern 10 (Meet (sig _)) => now apply SigMeet: typeclass_instances.
#[global]
Hint Extern 10 (Sup (sig _)) => now apply SigSup: typeclass_instances.
#[global]
Hint Extern 10 (Inf (sig _)) => now apply SigInf: typeclass_instances.
#[global]
Hint Extern 10 (Top (sig _)) => now apply SigTop: typeclass_instances.
#[global]
Hint Extern 10 (Bottom (sig _)) => now apply SigBottom: typeclass_instances.

#[global]
Instance SigJoinSemiLattice {A: Type} `{JoinSemiLattice A} (P: A -> Prop) (join_correct : StableJoin P):
  JoinSemiLattice (sig P).
Proof. now apply (projected_join_semi_lattice (@proj1_sig _ P)). Qed.

#[global]
Instance SigMeetSemiLattice {A: Type} `{MeetSemiLattice A} (P: A -> Prop) (meet_correct : StableMeet P):
  MeetSemiLattice (sig P).
Proof. now apply (projected_meet_semi_lattice (@proj1_sig _ P)). Qed.

#[global]
Instance SigLattice {A: Type} `{Lattice A} (P: A -> Prop)
    (join_correct : StableJoin P) (meet_correct : StableMeet P): Lattice (sig P) := {}.

#[global]
Instance SigCompleteLattice {A: Type} `{CompleteLattice A} (P: A -> Prop)
  (join_correct : StableJoin P) (meet_correct : StableMeet P)
  (sup_correct : StableSup P) (inf_correct : StableInf P)
  (top_correct: StableTop P) (bottom_correct: StableBottom P):
  CompleteLattice (sig P).
Proof.
  apply (projected_complete_lattice (@proj1_sig _ P)); try now auto.
  - cbv. reflexivity.
  - cbv. reflexivity.
Qed.

Lemma join_sup_comm {A: Type} `{CompleteLattice A}:
  forall (P Q: ℘ A), sup (P ⊔ Q) = (sup P) ⊔ (sup Q).
Proof.
  intros P Q. apply antisymmetry.
  - apply sup_lub. intros x [H__x | H__x].
     transitivity (sup P). now apply sup_ub. now apply join_ub.
    transitivity (sup Q). now apply sup_ub. now apply join_ub.
  - apply join_lub. split; apply sup_increasing; intros x H__x.
    now left. now right.
Qed.

Lemma meet_sup_comm {A: Type} `{CompleteLattice A}:
  forall (P Q: ℘ A), sup (P ⊓ Q) = (sup P) ⊓ (sup Q).
Proof.
  intros P Q. apply antisymmetry.
  - apply sup_lub. intros x [H__P H__Q]. apply meet_glb. split; now apply sup_ub.
  -
    transitivity (sup P).
     now apply meet_lb.
    apply sup_increasing.
    intros x H__P. unfold meet. unfold PowersetMeet.
    Admitted.

#[program]
Definition PreserveSupCompleteLattice {P Q: Type} `{CompleteLattice P} `{CompleteLattice Q} :=
  SigCompleteLattice (fun f : P -> Q => PreserveSup f) _ _ _ _ _ _.
Next Obligation.
  intros f g H__f H__g S.
  (* TODO: make the correct type classes/definitions transparent *)
  unfold sg_set_op. fold sup. unfold sg_op. unfold join. unfold PointwiseJoin.
  unfold PreserveSup in *. unfold PreserveSgSetOp in *.
  rewrite H__f. rewrite H__g.
  apply antisymmetry.
  - apply join_lub. split;
      apply sup_lub; intros x [y [H__y H__eq]]; subst;
      (transitivity ((f ⊔ g) y); [now apply join_ub | apply sup_ub; now exists y]).
  - rewrite <- join_sup_comm.
    apply sup_lub. intros y [x [H__x H__eq]]; subst.
    rewrite join_sup_comm. apply join_increasing; apply sup_ub; now exists x.
Qed.
Next Obligation.
  intros f g H__f H__g S.
  unfold sg_set_op. fold sup. unfold sg_op. unfold meet. unfold PointwiseMeet.
  unfold PreserveSup in *. unfold PreserveSgSetOp in *.
  rewrite H__f. rewrite H__g.
  apply antisymmetry.
  - rewrite <- H__f. rewrite <- H__g.
    apply sup_ub. unfold image.
  - apply meet_glb. split; apply sup_lub; intros y [x [H__x H__eq]]; subst.
     transitivity (f x). now apply meet_lb. apply sup_ub. now exists x.
    transitivity (g x). now apply meet_lb. apply sup_ub. now exists x.
  - rewrite <- join_sup_comm.
    apply sup_lub. intros y [x [H__x H__eq]]; subst.
    rewrite join_sup_comm. apply join_increasing; apply sup_ub; now exists x.
Qed.
