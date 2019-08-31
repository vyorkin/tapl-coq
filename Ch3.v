Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From Coq Require Import ssreflect.

Module Bool.

  Inductive term : Type :=
  | true
  | false
  | ifelse : term -> term -> term -> term.

  (* lets introduce a notation for expressiveness *)
  Notation "'if' c 'then' t1 'else' t2" := (ifelse c t1 t2).

  (* evaluation relation on terms *)
  Reserved Notation "t ==> t'" (at level 50).

  Inductive eval_step : term -> term -> Prop :=
  | E_IfTrue : forall t2 t3, (if true then t2 else t3) ==> t2
  | E_IfFalse : forall t2 t3, (if false then t2 else t3) ==> t3
  | E_If : forall t1 t1' t2 t3,
      t1 ==> t1' -> (if t1 then t2 else t3) ==> (if t1' then t2 else t3)
  where "t ==> t'" := (eval_step t t').

  Example ex_inst_e_iftrue :
    (if true then true else (if false then false else false)) ==> true.
  Proof.
    apply E_IfTrue.
  Qed.

  Definition s := if true then false else false.
  Definition t := if s then true else true.
  Definition u := if false then true else true.

  Example ex3_5_3 :
    (if t then false else false) ==> (if u then false else false).
  Proof.
    apply E_If.
    apply E_If.
    apply E_IfTrue.
  Qed.

  Theorem one_step_eval_is_det :
    forall t t' t'' : term,
      (t ==> t') /\ (t ==> t'') -> t' = t''.
    Proof.
      move => t t' t'' H.
    Abort.

End Bool.

Module Arith.

  Inductive term : Type :=
  | term_true
  | term_false
  | term_cond : term -> term -> term -> term
  | term_zero
  | term_succ : term -> term
  | term_pred : term -> term
  | term_iszero : term -> term.

End Arith.
