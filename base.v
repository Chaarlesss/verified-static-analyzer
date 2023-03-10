From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
Import ListNotations.

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (s : string)
  | AMinus (a1 a2 : aexp).

Inductive bexp : Type :=
  | BLe (a1 a2 : aexp)
  | BNand (b1 b2 : bexp).

Definition label : Type := nat.
Definition value : Type := nat.
Definition variable : Type := string.

Inductive stmt: Type :=
  | SAssign (l: label) (l': label) (v : variable) (a : aexp)
  | SSkip (l: label)
  | SIf (l: label) (l': label) (b : bexp) (s1 : stmt)
  | SIfElse (l: label) (l': label) (b : bexp) (s1 : stmt) (s2 : stmt)
  | SWhile (l: label) (l': label) (b : bexp) (s : stmt)
  | SBreak (l: label) (l': label)
  | SCompound (l: label) (l': label) (list : list stmt).

Definition at_stmt (s: stmt): label :=
  match s with
  | SAssign l _ _ _ => l
  | SSkip l => l
  | SIf l _ _ _ => l
  | SIfElse l _ _ _ _ => l
  | SWhile l _ _ _ => l
  | SBreak l _ => l
  | SCompound l _ _ => l
  end.

Inductive trace_action : Type :=
  | TAssign (v : variable) (a : aexp) (v : value)
  | TBValid (b : bexp)
  | TBInvalid (b : bexp)
  | TBreak
  | TSkip.

Inductive finite_trace : Type :=
  | finite_trace_nil (l : label)
  | finite_trace_cons (l : label) (a : trace_action) (t : finite_trace).

CoInductive infinite_trace : Type :=
  | infinite_trace_cons (l : label) (a : trace_action) (t : infinite_trace).

Inductive trace : Type :=
  | finite : finite_trace -> trace
  | infinite : infinite_trace -> trace.

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

Definition after_trace (t : trace) : option label :=
  match t with
  | finite t' => Some (after_finite_trace t')
  | infinite t' => None
  end.

Fixpoint concat_finite (t1: finite_trace) (t2: finite_trace) : option (finite_trace) :=
  match t1 with
  | finite_trace_nil l1 =>
      let l2 := at_finite_trace t2 in
      if Nat.eqb l1 l2 then Some t2 else None
  | finite_trace_cons l1 a t1' =>
      match concat_finite t1' t2 with
      | Some t2' => Some (finite_trace_cons l1 a t2')
      | None => None
      end
  end.

Fixpoint concat_infinite (t1: finite_trace) (t2: infinite_trace) : option (infinite_trace) :=
  match t1 with
  | finite_trace_nil l1 =>
      let l2 := at_infinite_trace t2 in
      if Nat.eqb l1 l2 then Some t2 else None
  | finite_trace_cons l1 a t1' =>
      match concat_infinite t1' t2 with
      | Some t2' => Some (infinite_trace_cons l1 a t2')
      | None => None
      end
  end.

Definition concat (t1: trace) (t2: trace) : option trace :=
  match t1, t2 with
  | finite t1', finite t2' =>
      match concat_finite t1' t2' with
      | Some t => Some (finite t)
      | None => None
      end
  | finite t1', infinite t2' =>
      match concat_infinite t1' t2' with
      | Some t => Some (infinite t)
      | None => None
      end
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

Definition env : Type := variable -> value.

Fixpoint aeval (a: aexp) (ρ: env) : value :=
  match a with
  | ANum n => n
  | AId v => ρ v
  | AMinus a1 a2 => (aeval a1 ρ) - (aeval a2 ρ)
  end.

Definition trace_set : Type := trace -> Prop.

Definition empty_trace_set : trace_set := fun _ => False.
Definition singleton_trace_set : trace -> trace_set := fun t0 t => t0 = t.
Definition join_trace_set : trace_set -> trace_set -> trace_set :=
  fun s1 s2 t => s1 t \/ s2 t.

Definition prefix_trace_semantics (s: stmt) (t: finite_trace) : trace_set :=
  if (Nat.eqb (after_finite_trace t) (at_stmt s)) then
    match s with
    | SAssign l l' x a =>
        join_trace_set
          (singleton_trace_set (finite (finite_trace_nil l)))
          (fun t' => exists val, t' = finite (finite_trace_cons l (TAssign x a val) (finite_trace_nil l')) /\
                           val = aeval a (value_of t))
    | SSkip l => singleton_trace_set (finite (finite_trace_nil l))
    | SWhile l l' b s => empty_trace_set
    | _ => empty_trace_set
    end
  else
    empty_trace_set.
