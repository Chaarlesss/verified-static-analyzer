From Coq Require Import Relations.Relations.
From Coq Require Import Classes.RelationClasses.
From VSA Require Import Basics.
From VSA Require Import Lattice.

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

Class JoinStrict {A B: Type} (f: A -> B) `{Equiv A} `{Equiv B} `{Join A} `{Join B}: Prop :=
  join_strict : forall x y, f (x ⊔ y) = f x ⊔ f y.

Class MeetStrict {A B: Type} (f: A -> B) `{Equiv A} `{Equiv B} `{Meet A} `{Meet B}: Prop :=
  meet_strict : forall x y, f (x ⊓ y) = f x ⊓ f y.

(* TODO: split these defitions to consider non-empty sup strict and infimum strict *)
Class SupStrict {A B: Type} (f: A -> B) `{Equiv A} `{Equiv B} `{Sup A} `{Sup B}: Prop :=
  sup_strict : forall (S: ℘ A), f (sup S) = sup (image f S).

Class InfStrict {A B: Type} (f: A -> B) `{Equiv A} `{Equiv B} `{Inf A} `{Inf B}: Prop :=
  inf_strict : forall (S: ℘ A), f (inf S) = inf (image f S).

#[export]
Typeclasses Transparent JoinStrict MeetStrict SupStrict InfStrict.
