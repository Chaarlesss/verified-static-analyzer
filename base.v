From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From Coq Require Import Arith.
From VSA Require Import Lattice.

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

Inductive trace_action : Type :=
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
Inductive trace: Type :=
  | finite: finite_trace -> trace
  | infinite : infinite_trace -> trace.

Coercion finite_trace_nil : label >-> finite_trace.

Definition at_finite_trace (t : finite_trace) : label :=
  match t with
  | finite_trace_nil l => l
  | finite_trace_cons l _ _ => l
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

Fixpoint after_finite_trace (t : finite_trace) : label :=
  match t with
  | finite_trace_nil l => l
  | finite_trace_cons _ _ t' => after_finite_trace t'
  end.

Notation "'at⟦' S ⟧" := (at_stmt S).
Notation "'at⟦' π '⟧t'" := (at_finite_trace π).
Notation "'after⟦' π '⟧t'" := (after_finite_trace π).

Program Fixpoint concat_finite (t1 t2: finite_trace) {_: after⟦t1⟧t = at⟦t2⟧t}: finite_trace :=
  match t1 with
  | finite_trace_nil _ => t2
  | finite_trace_cons l a t1' => finite_trace_cons l a (@concat_finite t1' t2 _)
  end.

Notation "t1 ⁀ t2" := (concat_finite t1 t2) (at level 40).
Notation "l ⟶( a ) π" := (finite_trace_cons l a π) (at level 50).

Program Fixpoint concat_infinite (t1: finite_trace) (t2: infinite_trace) {_: after⟦t1⟧t = at_infinite_trace t2}: infinite_trace :=
  match t1 with
  | finite_trace_nil _ => t2
  | finite_trace_cons l a t1' => infinite_trace_cons l a (@concat_infinite t1' t2 _)
  end.

Program Definition concat (t1 t2: trace) : option trace :=
  match t1, t2 with
  | finite t1', finite t2' =>
      if Nat.eq_dec after⟦t1'⟧t at⟦t2'⟧t then Some (finite (@concat_finite t1' t2' _))
      else None
  | finite t1', infinite t2' =>
      if Nat.eq_dec after⟦t1'⟧t (at_infinite_trace t2') then Some (infinite (@concat_infinite t1' t2' _))
      else None
  | infinite _, _ => Some t1
  end.

Definition value_of (t: finite_trace) (v: variable) : value :=
  let f :=
    (fix f (t: finite_trace) : option value :=
       match t with
       | finite_trace_nil _ => None
       | finite_trace_cons _ (TAssign s' _ val') t' =>
            match f t' with
            | Some val => Some val
            | None => if String.eqb v s' then Some val' else None
            end
       | finite_trace_cons _ _ t' => f t'
       end
    )
  in
  match f t with
  | Some v => v
  | None => 0
  end.

Notation "'ϱ(' π ')'" := (value_of π).

Inductive deductive_prefix_trace_semantics (l': label) (π: finite_trace): stmt -> ℘ finite_trace :=
  | dpts_stmt :
    forall S, at⟦S⟧ = after⟦π⟧t -> deductive_prefix_trace_semantics l' π S after⟦π⟧t
  | dpts_assign :
    forall x a, deductive_prefix_trace_semantics l' π (SAssign after⟦π⟧t x a) (after⟦π⟧t ⟶(TAssign x a (A⟦a⟧ϱ(π))) l')
  | dpts_while_false :
    forall b S π' (H: after⟦π⟧t = at⟦π'⟧t), after⟦π⟧t = after⟦π'⟧t -> B⟦b⟧ϱ(@concat_finite π π' H) = false ->
      deductive_prefix_trace_semantics l' π (SWhile after⟦π⟧t b S) (after⟦π⟧t ⟶(TBInvalid b) l').

Definition fixpoint_prefix_trace_semantics (l': label) (π: finite_trace) (S: stmt): ℘ finite_trace :=
  let l := after⟦π⟧t in
  if (Nat.eqb at⟦S⟧ l) then
    match S with
    | SAssign _ x a => {{ finite_trace_nil l }} ∪ {{ l ⟶(TAssign x a (A⟦a⟧ϱ(π))) l' }}
    | _ => {{ l }}
    end
  else
    ∅.
