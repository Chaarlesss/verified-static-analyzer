From Coq Require Import Program.Program.
From VSA Require Import Basics.
From VSA Require Import Functions.
From VSA Require Import Lattice.
From VSA Require Import LatticeProperties.
From VSA Require Import Galois.

Import SetNotations.

Variable P Q: Type.
Context `{Setoid P} `{Setoid Q}.

#[program]
Definition post (R: ℘ (P * Q)): { f : (℘ P -> ℘ Q) | PreserveSup f } :=
  fun p y => exists x, x ∈ p /\ R (x, y).
Next Obligation.
  intros S y. split.
  - intros [x [[T [H__T H__x]] H__R]]. exists (fun y' => exists x', T x' /\ R (x', y')). firstorder.
  - intros [T1 [[T [H__T H__T1]] H__y]]; subst. firstorder.
Qed.

Definition post_inv (T: { f : (℘ P -> ℘ Q) | PreserveSup f }): ℘ (P * Q) :=
  fun xy => (snd xy) ∈ `T {{ (fst xy) }}.

(*
Definition post_dual (R: ℘ (P * Q)): ℘ P -> ℘ Q :=
  fun p => ¬ (post R (¬ p)). *)

Print GaloisConnection.

#[program]
Instance post_post_inv_connection:
  GaloisConnection (℘ (P * Q)) ({ f : (℘ P -> ℘ Q) | PreserveSup f }) post post_inv.
Next Obligation.
  split; intros H.
  - intros xy H__xy. apply H. exists (fst xy). split.
     reflexivity.
    rewrite <- surjective_pairing with P Q xy. assumption.
  - intros p y [x [H__x H__R]].
    unfold gamma in H. unfold post_inv in H.
    unfold ord in H. unfold PowersetOrd in H.
    assert (Q0 {{ x }} ⊆ Q0 p).
    {
      intros y' H'.
    }
    simpl.
    (* Decomposition of a set into each element??? *)
    (* Use the fact that it is U-morphism *)
    apply H.

*)
