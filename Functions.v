From Coq Require Import Relations.Relations.
From Coq Require Import Classes.RelationClasses.
From VSA Require Import Basics.

Import SetNotations.

(* The definition of image here is maybe to coarse *)
(* but we don't have the choice (for now) to use this *)
(* a proper solution would include a rewrite of the set "library" *)
(* to define the classical operations over sets as morphism *)
(* For instance, we are not able to prove that if two elements are equivalents *)
(* and one of them is in a set, then the other is also in the set (because it is the same element) *)
Definition image {X A: Type} (f : X -> A) (S : ℘ X) : ℘ A :=
   fun y => exists x, x ∈ S /\ y ≡ f x.

Class Increasing {A B: Type} (f: A -> B) `{Poset A} `{Poset B}: Prop :=
  increasing : forall x y, x ⊑ y -> f x ⊑ f y.

Class Injective {A B: Type} (f: A -> B) `{Equiv A} `{Equiv B}: Prop :=
  injective : forall x y, f x = f y -> x = y.

Class Surjective {A B: Type} (f: A -> B) `{Equiv B}: Prop :=
  surjective : forall y, exists x, y = f x.

Class Bijective {A B: Type} (f: A -> B) `{Equiv A} `{Equiv B}: Prop :=
  bijective : exists (g: B -> A), (forall x, g (f x) = x) /\ (forall y, f (g y) = y).

#[export]
Typeclasses Transparent Increasing Injective Surjective Bijective.

Class PreserveSgOp {A B: Type} (f: A -> B) `{Equiv B} `(SgOp A) `(SgOp B): Prop :=
  preserve_sg_op : forall x y, f (x & y) = f x & f y.

Class PreserveSgSetOp {A B: Type} (f: A -> B) `{Equiv B} `(SgSetOp A) `(SgSetOp B): Prop :=
  preserve_sg_set_op : forall (S: ℘ A), f (sg_set_op S) = sg_set_op (image f S).

Class StableSgOp {A : Type} (P: A -> Prop) `(SgOp A): Prop :=
  stable_sg_op : forall x y, P x -> P y -> P (x & y).

Class StableSgSetOp {A: Type} (P: A -> Prop) `(SgSetOp A): Prop :=
  stable_sg_set_op : forall (S: ℘ A), (forall x, x ∈ S -> P x) -> P (sg_set_op S).

#[export]
Typeclasses Transparent PreserveSgOp PreserveSgSetOp StableSgOp StableSgSetOp.
