From Coq Require Import Relations.Relations.
From Coq Require Import Setoids.Setoid.
From Coq Require Import Classes.Morphisms.
From Coq Require Import Classes.RelationClasses.
From VSA Require Import Basics.

#[program]
Definition Image {X A: Type} `{Equiv X} `{Setoid A} (f : X → A) (S : ℘ X) : ℘ A.
  refine {{ y | exists x, x ∈ S /\ y = f x }}.
  solve_proper.
Defined.

#[global]
Instance ImageProper {X A: Type} `{Setoid X} `{Setoid A}:
  Proper ((=) ==> (=) ==> (=)) (@Image X A _ _ _).
Proof.
  intros f g H__fg P Q H__PQ x. split; intros [z []]; exists z; firstorder.
Qed.

Class Increasing {A B: Type} `{Poset A} `{Poset B} (f: A → B): Prop :=
  increasing : forall x y, x ⊑ y -> f x ⊑ f y.

Class Injective {A B: Type} `{Equiv A} `{Equiv B} (f: A → B): Prop :=
  injective : forall x y, f x = f y -> x = y.

Class Surjective {A B: Type} `{Equiv A} `{Equiv B} (f: A → B): Prop :=
  surjective : forall y, exists x, y = f x.

Class Bijective {A B: Type} `{Equiv A} `{Equiv B} (f: A → B): Prop :=
  bijective : exists (g: B -> A), (forall x, g (f x) = x) /\ (forall y, f (g y) = y).

#[export]
Typeclasses Transparent Increasing Injective Surjective Bijective.

Class PreserveSgOp {A B: Type} `{Equiv A} `{Equiv B} (f: A → B) `(!SgOp A) `(!SgOp B): Prop :=
  preserve_sg_op : forall (x y: A), f (x & y) = f x & f y.

Class PreserveSgSetOp {A B: Type} `{Equiv A} `{Setoid B} (f: A → B) (SA: SgSetOp A) (SB: SgSetOp B): Prop :=
  preserve_sg_set_op : forall (S: ℘ A), f (SA S) = SB (Image f S).

(* Here, it is the first time we use the fact that a property (here P) can be seen as the *)
(* set of elements which verify it*)
Class StableSgOp {A : Type} `{Equiv A} (P: ℘ A) `(!SgOp A): Prop :=
  stable_sg_op : forall x y, P x -> P y -> P (x & y).

Class StableSgSetOp {A: Type} `{Equiv A} (P: ℘ A) (SA: SgSetOp A): Prop :=
  stable_sg_set_op : forall (S: ℘ A), (forall x, x ∈ S -> P x) -> P (SA S).

#[export]
Typeclasses Transparent PreserveSgOp PreserveSgSetOp StableSgOp StableSgSetOp.
