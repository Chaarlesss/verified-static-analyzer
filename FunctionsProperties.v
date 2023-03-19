From Coq Require Import Relations.Relations.
From Coq Require Import Classes.RelationClasses.
From VSA Require Import Basics.
From VSA Require Import Functions.

Import SetNotations.

Lemma image_set_increasing {X A: Type} (f: X -> A):
  Increasing (image f).
Proof. firstorder. Qed.
