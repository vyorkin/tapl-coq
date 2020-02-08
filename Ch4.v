Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From Coq Require Import ssreflect.

Module Ch4.
  Inductive term : Type :=
  | T_true
  | T_false
  | T_cond (cond t1 t2 : term)
  | T_zero
  | T_succ (n : term)
  | T_pred (n : term)
  | T_iszero (n : term).

  Fixpoint isnumericval t :=
    match t with
    | T_zero => true
    | T_succ t' => isnumericval t'
    | _ => false
    end.

  Compute (isnumericval T_true).
  Compute (isnumericval T_zero).
  Compute (isnumericval (T_succ T_true)).
  Compute (isnumericval (T_pred T_zero)).
  Compute (isnumericval (T_succ T_zero)).

  Fixpoint isval t :=
    match t with
    | T_true | T_false => true
    | t' => isnumericval t'
    end.

  Compute (isval (T_succ T_zero)).
  Compute (isval (T_succ (T_succ T_zero))).
  Compute (isval (T_pred (T_succ T_zero))).
  Compute (isval (T_pred (T_iszero T_zero))).

  (* Single-step evaluation (partial function) *)

  Fixpoint eval1 t :=
    match t with
    | T_cond T_true t _ =>
      Some t
    | T_cond T_false _ t =>
      Some t
    | T_cond cond t1 t2 =>
      match eval1 cond with
      | Some cond' => Some (T_cond cond' t1 t2)
      | None => None
      end
    | T_succ t' =>
      match eval1 t' with
      | Some v => Some (T_succ v)
      | None => None
      end
    | T_pred T_zero =>
      Some T_zero
    | T_pred t' =>
      if t' is T_succ t'' then
        if isnumericval t'' then (Some t'') else None
      else
        if eval1 t' is Some v then Some (T_pred v) else None
    | T_iszero T_zero =>
      Some T_true
    | T_iszero t' =>
      if t' is T_succ t'' then
        if isnumericval t'' then (Some T_false) else None
      else
        if eval1 t' is Some v then (Some (T_iszero v)) else None
    | _ =>
      None
    end.

End Ch4.
