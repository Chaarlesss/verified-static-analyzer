From Coq Require Import Relations.Relations.
From Coq Require Import Classes.RelationClasses.
From VSA Require Import Basics.

Import SetNotations.

Definition image {X A: Type} (f : X -> A) `{Equiv A} (S : ℘ X) : ℘ A :=
   fun y => exists x, x ∈ S /\ y = f x.

Class Increasing {A B: Type} (f: A -> B) `{Poset A} `{Poset B}: Prop :=
  increasing : forall x y, x ⊑ y -> f x ⊑ f y.

Class Injective {A B: Type} (f: A -> B) `{Equiv A} `{Equiv B}: Prop :=
  injective : forall x y, f x = f y -> x = y.

Class Surjective {A B: Type} (f: A -> B) `{Equiv A} `{Equiv B}: Prop :=
  surjective : forall y, exists x, y = f x.

Class Bijective {A B: Type} (f: A -> B) `{Equiv A} `{Equiv B}: Prop :=
  bijective : exists (g: B -> A), (forall x, g (f x) = x) /\ (forall y, f (g y) = y).

#[export]
Typeclasses Transparent Increasing Injective Surjective Bijective.

Class Strict {A B: Type} (f: A -> B) `{Equiv A} `{Equiv B} `{SgOp A} `{SgOp B}: Prop :=
  strict : forall x y, f (x & y) = f x & f y.

Class SetStrict {A B: Type} (f: A -> B) `{Equiv A} `{Equiv B} `{SgSetOp A} `{SgSetOp B}: Prop :=
  set_strict : forall (S: ℘ A), f (sg_set_op S) = sg_set_op (image f S).

#[export]
Typeclasses Transparent Strict SetStrict.
