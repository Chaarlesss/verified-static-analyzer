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
  Add Parametric Morphism: (⊔)
    with signature (=) ==> (=) ==> (=) as Join_Morphism.
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

  #[global]
  Add Parametric Morphism: sup
    with signature (=) ==> (=) as Sup_Morphism.
  Proof.
    intros P Q H__PQ. apply antisymmetry; apply sup_lub; intros x H__x; apply sup_ub.
      now rewrite <- H__PQ.
    now rewrite H__PQ.
  Qed.

End Sup.

Section Inf.

  Context {A: Type} `{CompleteLattice A}.

  Lemma inf_lb:
    forall (S: ℘ A) x, x ∈ S -> inf S ⊑ x.
  Admitted.

  (* Lemma inf_decreasing *)

  #[global]
  Add Parametric Morphism: inf
    with signature (=) ==> (=) as Inf_Morphism.
  Proof.
    intros P Q H__PQ. apply antisymmetry; apply inf_glb; intros x H__x; apply inf_lb.
      now rewrite H__PQ.
    now rewrite <- H__PQ.
  Qed.

End Inf.

Section AlternativeOperators.

  Context {A: Type} `{Poset A}.

  Definition Join_Sup (S: Sup A): Join A := fun x y => sup {{ x; y }}.

  Definition Meet_Sup (S: Sup A): Meet A.
    refine (fun y z => @sup _ _ S {{{ x | x ⊑ y /\ x ⊑ z }}}).
    solve_proper.
  Defined.

  Definition Inf_Sup (S: Sup A): Inf A.
    refine (fun (P: ℘ A) => @sup _ _ S {{{ x | forall y, y ∈ P -> x ⊑ y }}}).
    solve_proper.
  Defined.

  Definition Top_Sup (S: Sup A): Top A := sup SetFull.
  Definition Bottom_Sup {A: Type} `{Setoid A} (S: Sup A): Bottom A := sup ∅.

  Definition Join_Inf (I: Inf A): Join A.
    refine (fun y z => @inf _ _ I {{{ x | y ⊑ x /\ z ⊑ x }}}).
    solve_proper.
  Defined.

  Definition Meet_Inf (I: Inf A): Meet A := fun x y => inf {{ x; y }}.

  Definition Sup_Inf (I: Inf A): Sup A.
    refine (fun (S: ℘ A) => @inf _ _ I {{{ x | forall y, y ∈ S -> y ⊑ x }}}).
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
       intros [H__x H__y]. eapply sup_lub. (* TODO: provide better way to do this kind of reasoning? *)
       Unshelve. 4: { refine {{{ z | z ⊑ x /\ z ⊑ y }}}. solve_proper. }. reflexivity.
       (* TODO: auto unfold *)
       unfold SetContains. unfold sett. unfold SetProp. auto.
      intros H__u. split; transitivity (Meet_Sup S x y); auto; apply sup_lub; now intros z [H__x H__y].
  - intros Q u. unfold inf. unfold Inf_Sup. split.
     intros H__u x H__x.
     etransitivity. apply H__u. apply sup_lub. now auto.
    intros H__u. remember {{{ x | forall y : A, y ∈ Q -> x ⊑ y}}} as SS.
    apply sup_lub with SS. reflexivity.
    unfold SetContains. rewrite HeqSS. unfold sett. simpl. apply H__u.
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

  Context (X A: Type) `{!Equiv X} `{!Equiv A} `{!Ord A} `{!Join A} `{!Meet A} `{!Sup A} `{!Inf A} `{!Top A} `{!Bottom A}.

  #[export]
  Instance PointwiseJoin `{!JoinSemiLattice A}: Join (X → A).
    refine (fun f g => λ x ⇒ f x ⊔ g x).
    solve_proper.
  Defined.

  #[export]
  Instance PointwiseMeet `{!MeetSemiLattice A}: Meet (X → A).
    refine (fun f g => λ x ⇒ f x ⊓ g x).
    solve_proper.
  Defined.

  #[export]
  Instance PointwiseSup `{!CompleteLattice A}: Sup (X → A).
    (* TODO: ugly proof *)
    unshelve refine (fun (S: ℘ (X → A)) => λ x ⇒ sup {{{ a | exists f, f ∈ S /\ a = f x }}}).
    5: { solve_proper. }
    apply Sup0. apply CompleteLattice0.
    intros P Q H__PQ.
    (* TODO: custom f_equal *)
    remember ({{{ a | exists f : X → A, f ∈ S /\ a = f P}}}) as S1.
    remember ({{{ a | exists f : X → A, f ∈ S /\ a = f Q}}}) as S2.
    assert (S1 = S2).
    {
      apply poset_antisym; subst; intros x [f [H__f H__x]].
      - exists f. split; auto. now rewrite <- H__PQ.
      - exists f. split; auto. now rewrite H__PQ.
    }
    now rewrite H.
  Defined.

  #[export]
  Instance PointwiseInf `{!CompleteLattice A}: Inf (X → A).
    unshelve refine (fun (S: ℘ (X → A)) => λ x ⇒ inf {{{ a | exists f, f ∈ S /\ a = f x }}}).
    4: { apply Equiv1. }
    4: { solve_proper. }
    apply Inf0. apply CompleteLattice0.
    intros P Q H__PQ.
    remember ({{{ a | exists f : X → A, f ∈ S /\ a = f P}}}) as S1.
    remember ({{{ a | exists f : X → A, f ∈ S /\ a = f Q}}}) as S2.
    assert (S1 = S2).
    {
      apply poset_antisym; subst; intros x [f [H__f H__x]].
      - exists f. split; auto. now rewrite <- H__PQ.
      - exists f. split; auto. now rewrite H__PQ.
    }
    now rewrite H.
  Defined.

  #[export]
  Instance PointwiseTop `{!CompleteLattice A}: Top (X → A).
    refine (λ _ ⇒ ⊤).
    instantiate (1 := _).
    firstorder.
  Defined.

  #[export]
  Instance PointwiseBottom `{!CompleteLattice A}: Bottom (X → A).
    refine (λ _ ⇒ ⊥).
    instantiate (1 := _).
    firstorder.
  Defined.

  #[program, export]
  Instance PointwiseJoinSemiLattice `{!JoinSemiLattice A}: JoinSemiLattice (X → A).
  Next Obligation.
    split.
    - intros [? ?] ?. apply join_lub. auto.
    - intros H__join. split; intros x0; (transitivity (x x0 ⊔ y x0); [apply join_ub | apply H__join]).
  Qed.

  #[program, export]
  Instance PointwiseMeetSemiLattice `{!MeetSemiLattice A}: MeetSemiLattice (X → A).
  Next Obligation.
    split.
    - intros [? ?] ?. apply meet_glb. auto.
    - intros H__meet. split; intros x0; (transitivity (x x0 ⊓ y x0); [apply H__meet | apply meet_lb]).
  Qed.

  #[program, export]
  Instance PointwiseLattice `{!Lattice A}: Lattice (X → A).

  #[program, export]
  Instance PointwiseCompleteLattice `{!CompleteLattice A}: CompleteLattice (X → A).
  Next Obligation.
    split.
    - intros H f H__f x. transitivity (sup S x); auto.
      simpl. apply sup_ub. now exists f.
    - intros H x. simpl. apply sup_lub. intros a [g [H__g H__a]]. rewrite H__a. now apply H.
  Qed.
  Next Obligation.
    split.
    - intros H f H__f x. transitivity (inf S x); auto.
      simpl. apply inf_lb. now exists f.
    - intros H x. simpl. apply inf_glb. intros a [g [H__g H__a]]. rewrite H__a. now apply H.
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
  Instance PowersetJoin : Join (℘ X).
    refine (fun P Q => {{{ x | x ∈ P \/ x ∈ Q }}}).
    solve_proper.
  Defined.

  #[export]
  Instance PowersetMeet : Meet (℘ X).
    refine (fun P Q => {{{ x | x ∈ P /\ x ∈ Q}}}).
    solve_proper.
  Defined.

  #[export]
  Instance PowersetSup : Sup (℘ X).
    refine (fun (S: ℘ (℘ X)) => {{{ x | exists P, P ∈ S /\ x ∈ P }}}).
    solve_proper.
  Defined.

  #[export]
  Instance PowersetInf : Inf (℘ X).
    refine (fun (S: ℘ (℘ X)) => {{{ x | forall P, P ∈ S -> x ∈ P }}}).
    solve_proper.
  Defined.

  #[export]
  Instance PowersetTop : Top (℘ X) := SetFull.
  #[export]
  Instance PowersetBottom : Bottom (℘ X) := ∅.

  #[program, export]
  Instance PowersetMeetSemiLattice: MeetSemiLattice (℘ X).
  Next Obligation.
    split.
     intros [H__x H__y] e H__e. specialize (H__x e). specialize (H__y e). simpl in *; firstorder.
    intros H__u. split; intros e H__e; specialize (H__u e); simpl in *; firstorder.
  Qed.

  #[program, export]
  Instance PowersetJoinSemiLattice: JoinSemiLattice (℘ X).
  Next Obligation.
    split.
     intros [H__x H__y] e H__e. specialize (H__x e). specialize (H__y e). simpl in *. firstorder.
    intros H__u. split; intros e H__e; specialize (H__u e); simpl in *; firstorder.
  Qed.

  #[program, export]
  Instance PowersetLattice: Lattice (℘ X).

  #[program, export]
  Instance PowersetCompleteLattice: CompleteLattice (℘ X).
  Next Obligation.
    split.
    - intros H__u x H__x. transitivity (sup S); auto.
      intros t H__t. now exists x.
    - intros H__u t [v [H__v H__t]]. now apply (H__u v).
  Qed.
  Next Obligation.
    split.
    - intros H__u x H__x. transitivity (inf S); firstorder.
    - intros H__u t H__t v H__v. firstorder.
  Qed.
  Next Obligation.
    intros t H__t. now simpl.
  Qed.
  Next Obligation.
    intros t H__t. contradiction.
  Qed.

End Powerset.

Section Projection.

  Context {A B: Type} `{!Equiv A} `{!Ord A} `{!Join A} `{!Meet A} `{!Sup A} `{!Inf A} `{!Top A} `{!Bottom A}.

  Lemma projected_join_semi_lattice `{JoinSemiLattice B} (f: A → B)
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

  Lemma projected_meet_semi_lattice `{MeetSemiLattice B} (f: A → B)
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

  Lemma projected_lattice `{Lattice B} (f: A → B)
    (eq_correct : forall x y, x = y <-> f x = f y)
    (ord_correct : forall x y, x ⊑ y <-> f x ⊑ f y)
    (join_correct : PreserveJoin f)
    (meet_correct : PreserveMeet f): Lattice A.
  Proof.
    constructor.
    now apply (projected_join_semi_lattice f).
    now apply (projected_meet_semi_lattice f).
  Qed.

  Definition Build_ProjectedCompleteLattice `{CompleteLattice B} (f: A → B)
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
  Definition alt2_Build_ProjectedCompleteLattice `{CompleteLattice B} (f: A → B)
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

Definition SigJoin {A: Type} `{!Equiv A} `{!Join A} (P: ℘ A) (join_correct: StableJoin P): Join (sig P) :=
  fun x y => (`x ⊔ `y) ↾ (join_correct _ _ (proj2_sig x) (proj2_sig y)).

Definition SigMeet {A: Type} `{!Equiv A} `{!Meet A} (P: ℘ A) (meet_correct: StableMeet P): Meet (sig P) :=
  fun x y => (`x ⊓ `y) ↾ (meet_correct _ _ (proj2_sig x) (proj2_sig y)).

Definition SigSup {A: Type} `{CompleteLattice A} (P: ℘ A) (sup_correct: StableSup P): Sup (sig P).
  unshelve refine (fun (S: ℘ { x: A | P x }) => sup (Image proj1_sig_morphism S) ↾ _).
  apply sup_correct. intros x [[x' H__x'] [_ H__x]]. now rewrite H__x.
Defined.

Definition SigInf {A: Type} `{CompleteLattice A} (P: ℘ A) (inf_correct: StableInf P): Inf (sig P).
  unshelve refine (fun (S: ℘ { x: A | P x }) => inf (Image proj1_sig_morphism S) ↾ _).
  apply inf_correct. intros x [[x' H__x'] [_ H__x]]. now rewrite H__x.
Defined.

Definition SigTop {A: Type} `{!Equiv A} `{Top A} (P: ℘ A) (top_correct: StableTop P): Top (sig P) :=
  ⊤ ↾ top_correct.

Definition SigBottom {A: Type} `{!Equiv A} `{Bottom A} (P: ℘ A) (bottom_correct: StableBottom P): Bottom (sig P) :=
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
Instance SigJoinSemiLattice {A: Type} `{JoinSemiLattice A} (P: ℘ A) (join_correct : StableJoin P):
  JoinSemiLattice (sig P).
Proof. now apply (projected_join_semi_lattice proj1_sig_morphism). Qed.

#[global]
Instance SigMeetSemiLattice {A: Type} `{MeetSemiLattice A} (P: ℘ A) (meet_correct : StableMeet P):
  MeetSemiLattice (sig P).
Proof. now apply (projected_meet_semi_lattice proj1_sig_morphism). Qed.

#[global]
Instance SigLattice {A: Type} `{Lattice A} (P: ℘ A)
    (join_correct : StableJoin P) (meet_correct : StableMeet P): Lattice (sig P) := {}.

#[global]
Instance SigCompleteLattice {A: Type} `{CompleteLattice A} (P: ℘ A)
  (join_correct : StableJoin P) (meet_correct : StableMeet P)
  (sup_correct : StableSup P) (inf_correct : StableInf P)
  (top_correct: StableTop P) (bottom_correct: StableBottom P):
  CompleteLattice (sig P).
Proof.
  apply (Build_ProjectedCompleteLattice proj1_sig_morphism); try now auto.
  - cbv. reflexivity.
  - cbv. reflexivity.
Qed.

#[program]
Definition alt2_Build_SigCompleteLattice {A: Type} `{CompleteLattice A} (P: ℘ A)
  (sup_correct : StableSup P) := alt2_Build_ProjectedCompleteLattice (@proj1_sig_morphism _ _ P) _ _ _.
Next Obligation.
  now split.
Qed.
Next Obligation.
  now split.
Qed.
Next Obligation.
  repeat intro. reflexivity.
Qed.


(*Lemma join_sup_comm {A: Type} `{CompleteLattice A}:
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
Qed.*)

Definition singletons_set {A: Type} `{CompleteLattice A} (P: ℘ A): ℘ (℘ A).
  refine {{{ Q | exists x, x ∈ P /\ Q = {{ x }} }}}.
  solve_proper.
  Unshelve. apply H.
Defined.

Lemma set_decomposition {A: Type} `{CompleteLattice A}:
  forall (P: ℘ A), P = sup (singletons_set P).
Proof.
  intros P x. split.
  - intros H__x. exists {{ x }}. split.
     exists x. now intuition.
    now apply set_contains_singleton.
  - intros [S [[x' [H__x' H__S]] H__x]].
    assert (x = x') as H__eq. now apply H__S.
    now rewrite H__eq.
Qed.

Definition preservesup_set {P Q: Type} `{CompleteLattice P} `{CompleteLattice Q}: ℘ (P → Q).
  unshelve refine {{{ f | PreserveSup f }}}.
  apply H0. apply Sup0. apply Sup1.
  intros f g H__fg. split; intros H__f S.
  unfold PreserveSup in *. unfold PreserveSgSetOp in *.
  specialize (H__f S).
  assert (Image g S = Image f S). { now rewrite H__fg. }
  assert (Sup1 (Image g S) = Sup1 (Image f S)). { now rewrite H1. }
  rewrite H2.
  rewrite H1.
  rewrite H__fg in H__f.

#[program]
Definition PreserveSupCompleteLattice {P Q: Type} `{CompleteLattice P} `{CompleteLattice Q} `{CompleteLattice (P → Q)} :=
  alt2_Build_SigCompleteLattice {{{ f: (P → Q) | PreserveSup f }}} _.
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
