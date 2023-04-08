From Coq Require Import Program.Program.
From Coq Require Import Relations.Relations.
From Coq Require Import Setoids.Setoid.
From Coq Require Import Classes.Morphisms.
From Coq Require Import Classes.RelationClasses.
From VSA Require Import Basics.
From VSA Require Import Lattice.
From VSA Require Import Functions.

Section Join.

  Context {A: Type} `{JoinSemiLattice A}.

  Lemma join_ub:
    forall x y, x ⊑ (x ⊔ y) /\ y ⊑ (x ⊔ y).
  Proof.
    intros. apply join_lub. reflexivity.
  Qed.

  Lemma join_le:
    forall x y z, x ⊑ y \/ x ⊑ z -> x ⊑ y ⊔ z.
  Proof.
    intros x y z [H__x | H__x].
     transitivity y. assumption. now apply join_ub.
    transitivity z. assumption. now apply join_ub.
  Qed.

  Lemma join_le_l:
    forall x y z, x ⊑ y -> x ⊑ y ⊔ z.
  Proof. intros. apply join_le. now left. Qed.

  Lemma join_le_r:
    forall x y z, x ⊑ z -> x ⊑ y ⊔ z.
  Proof. intros. apply join_le. now right. Qed.

  Lemma join_idempotent:
    forall x, x ⊔ x = x.
  Proof.
    intros. apply antisymmetry.
    - apply join_lub. now split.
    - apply join_ub.
  Qed.

  Lemma join_comm:
    forall x y, x ⊔ y = y ⊔ x.
  Proof.
    intros. apply antisymmetry; apply join_lub; split; apply join_ub.
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

  (*Lemma sup_increasing:
    @Increasing (℘ A) A _ _ _ _ _ _ (sup).
  Proof.
    intros P Q H__S. apply sup_lub. intros x H__x%H__S. now apply sup_ub.
  Qed.

  Lemma sup_le:
    forall (P Q: ℘ A), (forall x, x ∈ P -> (exists x', x' ∈ Q /\ x ⊑ x')) -> sup P ⊑ sup Q.
  Proof.
    intros P Q H__elt. apply sup_lub. intros x H__x.
    destruct (H__elt x H__x) as [x' [H__x' H__ord]].
    transitivity x'. assumption. now apply sup_ub.
  Qed.*)

End Sup.

Section Inf.

  Context {A: Type} `{CompleteLattice A}.

  Lemma inf_lb:
    forall (S: ℘ A) x, x ∈ S -> inf S ⊑ x.
  Admitted.

  (* Lemma inf_decreasing *)

End Inf.

Section AlternativeOperators.

  Context {A: Type} `{Poset A}.

  Set Printing Implicit.

  Definition Join_Sup (S: Sup A): Join A := fun x y => sup {{ x; y }}.

  Definition Meet_Sup (S: Sup A): Meet A.
    refine (fun y z => @sup _ _ S {{ x | x ⊑ y /\ x ⊑ z }}).
    solve_proper.
  Defined.

  Definition Inf_Sup (S: Sup A): Inf A.
    refine (fun (P: ℘ A) => @sup _ _ S {{ x | forall y, y ∈ P -> x ⊑ y }}).
    solve_proper.
  Defined.

  Definition Top_Sup (S: Sup A): Top A := sup SetFull.
  Definition Bottom_Sup {A: Type} `{Setoid A} (S: Sup A): Bottom A := sup ∅.

  Definition Join_Inf (I: Inf A): Join A.
    refine (fun y z => @inf _ _ I {{ x | y ⊑ x /\ z ⊑ x }}).
    solve_proper.
  Defined.

  Definition Meet_Inf (I: Inf A): Meet A := fun x y => inf {{ x; y }}.

  Definition Sup_Inf (I: Inf A): Sup A.
    refine (fun (S: ℘ A) => @inf _ _ I {{ x | forall y, y ∈ S -> y ⊑ x }}).
    solve_proper.
  Defined.

  Definition Top_Inf (I: Inf A): Top A := inf ∅.
  Definition Bottom_Inf (I: Inf A): Bottom A := inf SetFull.

End AlternativeOperators.

Lemma alt1_Build_CompleteLattice (A: Type) `(Poset A) {S: Sup A} {I: Inf A}:
  (forall (S: ℘ A) u, (sup S) ⊑ u <-> (forall x, x ∈ S -> x ⊑ u)) ->
  (forall (S: ℘ A) u, u ⊑ (inf S) <-> (forall x, x ∈ S -> u ⊑ x)) ->
  @CompleteLattice A _ _ (Join_Sup S) (Meet_Inf I) S I (Top_Sup S) (Bottom_Inf I).
Proof.
  intros sup_lub inf_glb.
  constructor; auto.
  - constructor; constructor; auto.
    + intros x y u. split.
       intros [H__x H__y]. apply sup_lub. intros z [H__z| H__z]%set_contains_pair; now rewrite H__z.
      intros H__u. split; apply sup_lub with {{ x; y }}; auto; apply set_contains_pair; now intuition.
    + intros x y u. split.
       intros [H__x H__y]. apply inf_glb. intros z [H__z | H__z]%set_contains_pair; now rewrite H__z.
      intros H__u. split; apply inf_glb with {{ x; y }}; auto; apply set_contains_pair; now intuition.
  - intros x. now apply sup_lub with SetFull.
  - intros x. now apply inf_glb with SetFull.
Qed.

Lemma alt2_Build_CompleteLattice (A: Type) `(Poset A) {S: Sup A}:
  (forall (S: ℘ A) u, (sup S) ⊑ u <-> (forall x, x ∈ S -> x ⊑ u)) ->
  @CompleteLattice A _ _ (Join_Sup S) (Meet_Sup S) S (Inf_Sup S) (Top_Sup S) (Bottom_Sup S).
Proof.
  intros sup_lub.
  constructor; auto.
  - constructor; constructor; auto.
    + intros x y u. split.
       intros [H__x H__y]. apply sup_lub. intros z [H__z | H__z]%set_contains_pair; now rewrite H__z.
      intros H__u. split; apply sup_lub with {{ x; y }}; auto; apply set_contains_pair; now intuition.
    + intros x y u. split.
       intros [H__x H__y]. apply sup_lub with {{ z | z ⊑ x /\ z ⊑ y }}. reflexivity.
       (* TODO *)
       unfold SetContains. unfold sett. unfold SetProp. auto.
      intros H__u. split; transitivity (Meet_Sup S x y); auto; apply sup_lub; now intros z [H__x H__y].
  - intros Q u. unfold inf. unfold Inf_Sup. split.
     intros H__u x H__x. transitivity (sup (fun x : A => forall t, t ∈ Q -> x ⊑ t)); auto.
     apply sup_lub. now auto.
    intros H__u. now apply sup_lub with (fun x : A => forall t, t ∈ Q -> x ⊑ t).
  - intros x. now apply sup_lub with SetFull.
  - intros x. now apply sup_lub.
Qed.

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
  Instance PointwiseJoin: Join (X -> A) := fun f g (x: X) => f x ⊔ g x.
  #[export]
  Instance PointwiseMeet: Meet (X -> A) := fun f g (x: X) => f x ⊓ g x.
  #[export]
  Instance PointwiseSup: Sup (X -> A) := fun (S: ℘ (X -> A)) (x: X) => sup (fun a => exists f, f ∈ S /\ a = f x).
  #[export]
  Instance PointwiseInf: Inf (X -> A) := fun (S: ℘ (X -> A)) (x: X) => inf (fun a => exists f, f ∈ S /\ a = f x).
  #[export]
  Instance PointwiseTop: Top (X -> A) := fun _ => ⊤.
  #[export]
  Instance PointwiseBottom: Bottom (X -> A) := fun _ => ⊥.

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

  Context (X: Type) `{Setoid X}.

  #[export]
  Instance PowersetJoin : Join (℘ X) := fun P Q x => x ∈ P \/ x ∈ Q.
  #[export]
  Instance PowersetMeet : Meet (℘ X) := fun P Q x => x ∈ P /\ x ∈ Q.
  #[export]
  Instance PowersetSup : Sup (℘ X) := fun (S: ℘ (℘ X)) (x: X) => exists P, P ∈ S /\ x ∈ P.
  #[export]
  Instance PowersetInf : Inf (℘ X) := fun (S: ℘ (℘ X)) (x: X) => forall P, P ∈ S -> x ∈ P.
  #[export]
  Instance PowersetTop : Top (℘ X) := fun _ => True.
  #[export]
  Instance PowersetBottom : Bottom (℘ X) := fun _ => False.

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

  Context {A B: Type} `{!Equiv A} `{!Ord A} `{!Join A} `{!Meet A} `{!Sup A} `{!Inf A} `{!Top A} `{!Bottom A}.

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

  Definition Build_ProjectedCompleteLattice `{CompleteLattice B} (f: A -> B)
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
        apply ord_correct. now apply H0.
    - split; intros; apply ord_correct.
      * transitivity (f (inf S)).
         now apply ord_correct.
        (* TODO: idem *)
        rewrite inf_correct. apply inf_lb. exists x. now split.
      * rewrite inf_correct. apply inf_glb. intros y [x [H__x H__fx]]. rewrite H__fx.
        apply ord_correct. now apply H0.
    - intros x. apply ord_correct. rewrite top_correct. apply top_supremum.
    - intros x. apply ord_correct. rewrite bottom_correct. apply bottom_infimum.
  Defined.

  #[program]
  Definition alt2_Build_ProjectedCompleteLattice `{CompleteLattice B} (f: A -> B)
    (eq_correct : forall x y, x = y <-> f x = f y)
    (ord_correct : forall x y, x ⊑ y <-> f x ⊑ f y)
    (sup_correct : PreserveSup f) := alt2_Build_CompleteLattice A (projected_poset f eq_correct ord_correct) _.
  Next Obligation.
    split; intros; apply ord_correct.
    * transitivity (f (sup S)).
      (* TODO: lemma/tactic for this kind of trivial goal *)
       rewrite sup_correct. apply sup_ub. exists x. now split.
      now apply ord_correct.
    * rewrite sup_correct. apply sup_lub. intros y [x [H__x H__fx]]. rewrite H__fx.
      apply ord_correct. now apply H0.
  Defined.

End Projection.

Definition SigJoin {A: Type} `{!Equiv A} `{!Join A} (P: A -> Prop) `{!Proper ((=) ==> iff) P} (join_correct: StableJoin P): Join (sig P) :=
  fun x y => (`x ⊔ `y) ↾ (join_correct _ _ (proj2_sig x) (proj2_sig y)).

Definition SigMeet {A: Type} `{!Equiv A} `{!Meet A} (P: A -> Prop) `{!Proper ((=) ==> iff) P} (meet_correct: StableMeet P): Meet (sig P) :=
  fun x y => (`x ⊓ `y) ↾ (meet_correct _ _ (proj2_sig x) (proj2_sig y)).

#[program]
Definition SigSup {A: Type} `{Sup A} (P: A -> Prop) `{!Proper ((=) ==> iff) P} (sup_correct: StableSup P): Sup (sig P) :=
  fun (S: ℘ ({ x: A | P x })) => (sup (Image (@proj1_sig _ P) S)) ↾ _.
Next Obligation.
  apply sup_correct. intros x [[x' H__x'] [_ H__x]]. now rewrite H__x.
Defined.

#[program]
Definition SigInf {A: Type} `{Inf A} (P: A -> Prop) `{!Proper ((=) ==> iff) P} (inf_correct: StableInf P): Inf (sig P) :=
  fun (S: ℘ ({ x: A | P x })) => (inf (Image (@proj1_sig _ P) S)) ↾ _.
Next Obligation.
  apply inf_correct. intros x [[x' H__x'] [_ H__x]]. now rewrite H__x.
Defined.

Definition SigTop {A: Type} `{!Equiv A} `{Top A} (P: A -> Prop) `{!Proper ((=) ==> iff) P} (top_correct: StableTop P): Top (sig P) :=
  ⊤ ↾ top_correct.

Definition SigBottom {A: Type} `{!Equiv A} `{Bottom A} (P: A -> Prop) `{!Proper ((=) ==> iff) P}  (bottom_correct: StableBottom P): Bottom (sig P) :=
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
Instance SigJoinSemiLattice {A: Type} `{JoinSemiLattice A} (P: A -> Prop) `{!Proper ((=) ==> iff) P}  (join_correct : StableJoin P):
  JoinSemiLattice (sig P).
Proof. now apply (projected_join_semi_lattice (@proj1_sig _ P)). Qed.

#[global]
Instance SigMeetSemiLattice {A: Type} `{MeetSemiLattice A} (P: A -> Prop) `{!Proper ((=) ==> iff) P} (meet_correct : StableMeet P):
  MeetSemiLattice (sig P).
Proof. now apply (projected_meet_semi_lattice (@proj1_sig _ P)). Qed.

#[global]
Instance SigLattice {A: Type} `{Lattice A} (P: A -> Prop) `{!Proper ((=) ==> iff) P}
    (join_correct : StableJoin P) (meet_correct : StableMeet P): Lattice (sig P) := {}.

#[global]
Instance SigCompleteLattice {A: Type} `{CompleteLattice A} (P: A -> Prop) `{!Proper ((=) ==> iff) P}
  (join_correct : StableJoin P) (meet_correct : StableMeet P)
  (sup_correct : StableSup P) (inf_correct : StableInf P)
  (top_correct: StableTop P) (bottom_correct: StableBottom P):
  CompleteLattice (sig P).
Proof.
  apply (Build_ProjectedCompleteLattice (@proj1_sig _ P)); try now auto.
  - cbv. reflexivity.
  - cbv. reflexivity.
Qed.

#[program]
Definition alt2_Build_SigCompleteLattice {A: Type} `{CompleteLattice A} (P: A -> Prop) `{!Proper ((=) ==> iff) P}
  (sup_correct : StableSup P) := alt2_Build_ProjectedCompleteLattice (@proj1_sig _ P) _ _ _.
Next Obligation.
  now split.
Qed.
Next Obligation.
  now split.
Qed.
Next Obligation.
  repeat intro. reflexivity.
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

Lemma meet_sup_semicomm {A: Type} `{CompleteLattice A}:
  forall (P Q: ℘ A), sup (P ⊓ Q) ⊑ (sup P) ⊓ (sup Q).
Proof.
  intros P Q. apply sup_lub. intros x [H__P H__Q]. apply meet_glb. split; now apply sup_ub.
Qed.

Lemma set_decomposition {A: Type} `{CompleteLattice A}:
  forall (P: ℘ A), SetProper P -> P = sup {{S | exists x, x ∈ P /\ S = {{ x }} /\ SetProper S }}.
Proof.
  intros P H__P. apply poset_antisym. (* strange behavior *)
  - intros x H__x. exists {{ x }}. split.
     exists x. now intuition.
    now apply set_contains_singleton.
  - intros x [S [[x' [H__x' H__S]] H__x]].
    assert (x = x') as H__eq. now apply H__S.
    unfold SetContains.
    now rewrite H__eq.

#[program]
Definition PreserveSupCompleteLattice {P Q: Type} `{CompleteLattice P} `{CompleteLattice Q} :=
  alt2_Build_SigCompleteLattice (fun f : P -> Q => PreserveSup f) _.
Next Obligation.
  intros S H__S S'. apply antisymmetry.
  - apply sup_lub. intros y [f [H__f H__y]]. rewrite H__y. rewrite H__S; auto.
    apply sup_lub. intros z [x [H__x H__z]]; rewrite H__z.
    transitivity (sup (fun z => exists g, g ∈ S /\ z = g x)).
     apply sup_ub. exists f. now split.
    apply sup_ub. exists x. now split.
  - apply sup_lub. intros y [x [H__x H__y]]. rewrite H__y.
    apply sup_le. intros y' [f [H__f H__y']].
    exists (f (sup S')). split. exists f. now split.
    rewrite H__y'. rewrite H__S; auto. apply sup_ub. now exists x.
Qed.
