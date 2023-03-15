From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From Coq Require Import Arith.
From VSA Require Import Basics.
From VSA Require Import Lattice.
From VSA Require Import Functions.
From VSA Require Import Fixpoints.

Import SetNotations.

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (s : string)
  | AMinus (a1 a2 : aexp).

Inductive bexp : Type :=
  | BLe (a1 a2: aexp)
  | BAnd (b1 b2: bexp)
  | BOr (b1 b2: bexp)
  | BNot (b: bexp).

Definition label : Type := nat.
Definition value : Type := nat.
Definition variable : Type := string.
Definition env : Type := variable -> value.

Fixpoint aeval (a: aexp) (ρ: env) : value :=
  match a with
  | ANum n => n
  | AId v => ρ v
  | AMinus a1 a2 => (aeval a1 ρ) - (aeval a2 ρ)
  end.

Fixpoint beval (b: bexp) (ρ: env) : bool :=
  match b with
  | BLe a1 a2 => Nat.leb (aeval a1 ρ) (aeval a2 ρ)
  | BAnd b1 b2 => (beval b1 ρ) && (beval b2 ρ)
  | BOr b1 b2 => (beval b1 ρ) || (beval b2 ρ)
  | BNot b => negb (beval b ρ)
  end.

Notation "'A⟦' A '⟧' ρ" := (aeval A ρ) (at level 40).
Notation "'B⟦' B '⟧' ρ" := (beval B ρ) (at level 40).

Inductive stmt: Type :=
  | SAssign (l: label) (v : variable) (a : aexp)
  | SSkip (l: label)
  | SIf (l: label) (b : bexp) (s1 : stmt)
  | SIfElse (l: label) (b : bexp) (s1 : stmt) (s2 : stmt)
  | SWhile (l: label) (b : bexp) (s : stmt)
  | SBreak (l: label)
  | SCompound (list : stmt_list)
with stmt_list: Type :=
  | stmt_list_singleton (s: stmt)
  | stmt_list_cons (s: stmt) (list: stmt_list).

Fixpoint at_stmt (s: stmt): label :=
  match s with
  | SAssign l _ _ => l
  | SSkip l => l
  | SIf l _ _ => l
  | SIfElse l _ _ _ => l
  | SWhile l _ _ => l
  | SBreak l => l
  | SCompound list => at_stmt_list list
  end
with at_stmt_list (list: stmt_list): label :=
  match list with
  | stmt_list_singleton s => at_stmt s
  | stmt_list_cons s _ => at_stmt s
  end.

Variant trace_action : Type :=
  | TAssign (v : variable) (a : aexp) (v : value)
  | TBValid (b : bexp)
  | TBInvalid (b : bexp)
  | TBreak
  | TSkip.

Inductive finite_trace: Type :=
  | finite_trace_nil (l: label)
  | finite_trace_cons (l: label) (a : trace_action) (t : finite_trace).

CoInductive infinite_trace: Type :=
  | infinite_trace_cons (l: label) (a : trace_action) (t : infinite_trace).

(* implicitely a bi-inductive type *)
Variant trace: Type :=
  | finite: finite_trace -> trace
  | infinite : infinite_trace -> trace.

Coercion finite_trace_nil : label >-> finite_trace.

Fixpoint at_finite_trace (t : finite_trace) : label :=
  match t with
  | finite_trace_nil l => l
  | finite_trace_cons _ _ t' => at_finite_trace t'
  end.

Definition at_infinite_trace (t : infinite_trace) : label :=
  match t with
  | infinite_trace_cons l _ _ => l
  end.

Definition at_trace (t : trace) : label :=
  match t with
  | finite t' => at_finite_trace t'
  | infinite t' => at_infinite_trace t'
  end.

Definition after_finite_trace (t : finite_trace) : label :=
  match t with
  | finite_trace_nil l => l
  | finite_trace_cons l _ _ => l
  end.

Notation "'at⟦' S ⟧" := (at_stmt S).
Notation "'at⟦' π '⟧t'" := (at_finite_trace π).
Notation "'after⟦' π '⟧t'" := (after_finite_trace π).

#[program]
Fixpoint concat_finite (t1 t2: finite_trace) {_: after⟦t1⟧t ≡ at⟦t2⟧t}: finite_trace :=
  match t2 with
  | finite_trace_nil _ => t1
  | finite_trace_cons l a t2' => finite_trace_cons l a (@concat_finite t1 t2' _)
  end.

Notation "t1 ⁀ t2" := (concat_finite t1 t2) (at level 40).
Notation "π ⟶( a ) l" := (finite_trace_cons l a π) (at level 50).

#[program]
Fixpoint concat_infinite (t1: finite_trace) (t2: infinite_trace) {_: after⟦t1⟧t ≡ at_infinite_trace t2}: infinite_trace :=
  match t1 with
  | finite_trace_nil _ => t2
  | finite_trace_cons _ a t1' =>
      @concat_infinite t1' (infinite_trace_cons after⟦t1'⟧t a t2) _
  end.

#[program]
Definition concat (t1 t2: trace) : option trace :=
  match t1, t2 with
  | finite t1', finite t2' =>
      if Nat.eq_dec after⟦t1'⟧t at⟦t2'⟧t then Some (finite (@concat_finite t1' t2' _))
      else None
  | finite t1', infinite t2' =>
      if Nat.eq_dec after⟦t1'⟧t (at_infinite_trace t2') then Some (infinite (@concat_infinite t1' t2' _))
      else None
  | infinite _, _ => Some t1
  end.

Fixpoint value_of (t: finite_trace) (v: variable) : value :=
  match t with
  | finite_trace_nil _ => 0
  | finite_trace_cons _ (TAssign s' _ val) t' =>
      if String.eqb v s' then val else value_of t' v
  | finite_trace_cons _ _ t' => value_of t' v
  end.

Notation "'ϱ(' π ')'" := (value_of π).

(* l' is the label after the statement, and it is not necessarily the label at the end of the traces *)
Inductive deductive_prefix_trace_semantics (l': label): stmt -> finite_trace -> ℘ finite_trace :=
  | dpts_stmt :
    forall S π1, at⟦S⟧ ≡ after⟦π1⟧t -> deductive_prefix_trace_semantics l' S π1 after⟦π1⟧t
  | dpts_assign :
    forall x a π1, deductive_prefix_trace_semantics l' (SAssign after⟦π1⟧t x a) π1 (after⟦π1⟧t ⟶(TAssign x a (A⟦a⟧ϱ(π1))) l')
  | dpts_while_false :
    forall b S π1 π2 (H: after⟦π1⟧t ≡ at⟦π2⟧t), after⟦π1⟧t ≡ after⟦π2⟧t -> B⟦b⟧ϱ(@concat_finite π1 π2 H) ≡ false ->
      deductive_prefix_trace_semantics l' (SWhile after⟦π1⟧t b S) π1 (π2 ⟶(TBInvalid b) l')
  | dpts_while_true :
    forall b S π1 π2 π3 (H1: after⟦π1⟧t ≡ at⟦π2⟧t) (H2: at⟦S⟧ ≡ at⟦π3⟧t), after⟦π1⟧t ≡ after⟦π2⟧t ->
      B⟦b⟧ϱ(@concat_finite π1 π2 H1) ≡ true ->
      deductive_prefix_trace_semantics after⟦π1⟧t S ((@concat_finite π1 π2 H1) ⟶(TBValid b) at⟦S⟧) π3 ->
      deductive_prefix_trace_semantics l' (SWhile after⟦π1⟧t b S) π1 (@concat_finite (π2 ⟶(TBValid b) at⟦S⟧) π3 H2).

(* TODO: find a way to express a set based on a condition *)
Axiom F_while : label -> bexp -> stmt -> (finite_trace -> ℘ finite_trace) -> (finite_trace -> ℘ finite_trace).
Instance finite_trace_Equiv: Equiv finite_trace := eq.
#[local]
Instance finite_trace_wp_finite_trace_CompleteLattice : CompleteLattice (finite_trace -> ℘ finite_trace).
Proof.
  apply PointwiseCompleteLattice.
  apply PowersetCompleteLattice.
Defined.
#[local]
Instance F_while_Increasing l b S: Increasing (F_while l b S).
Admitted.

Definition fixpoint_prefix_trace_semantics (l': label) (S: stmt) (π1: finite_trace): ℘ finite_trace :=
  let l := after⟦π1⟧t in
  if (Nat.eqb at⟦S⟧ l) then
    match S with
    | SAssign _ x a => {{ finite_trace_nil l }} ∪ {{ l ⟶(TAssign x a (A⟦a⟧ϱ(π1))) l' }}
    | SWhile _ b s => lfp_tarski (F_while l b s) π1
    | _ => {{ l }}
    end
  else
    ∅.
