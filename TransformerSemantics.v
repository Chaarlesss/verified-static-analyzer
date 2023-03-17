From VSA Require Import Basics.
From VSA Require Import Functions.
From VSA Require Import Lattice.
From VSA Require Import LatticeProperties.
From VSA Require Import Galois.

Import SetNotations.

Variable P Q: Type.
Context `{Setoid P} `{Setoid Q}.

Definition post (R: ℘ (P * Q)): ℘ P -> ℘ Q :=
  fun p y => exists x, x ∈ p /\ R (x, y).

Definition post_inv (T: ℘ P -> ℘ Q): ℘ (P * Q) :=
  fun xy => (snd xy) ∈ T {{ (fst xy) }}.

Definition post_dual (R: ℘ (P * Q)): ℘ P -> ℘ Q :=
  fun p => ¬ (post R (¬ p)).

(* TODO: show it is a poset *)
Check { f : (℘ P -> ℘ Q) | PreserveSup f }.

(*
#[program]
Instance post_post_inv_connection:
  GaloisConnection (℘ (P * Q)) (℘ P -> ℘ Q) post post_inv.
Next Obligation.
  split; intros H.
  - intros xy H__xy.
    apply H. exists (fst xy).
    split.
    + reflexivity.
    + rewrite <- surjective_pairing with P Q xy. assumption.
  - intros p y [x [H__x H__R]].
    unfold gamma in H. unfold post_inv in H.
    unfold ord in H. unfold PowersetOrd in H.
    (* Use the fact that it is U-morphism *)
    apply H.

*)
