Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From Coq Require Import ssreflect.

Module Ch3.

  Inductive term : Type :=
  | T_true
  | T_false
  | T_cond (cond t1 t2 : term).

  (* Let's introduce a custom grammar entry for expressiveness *)

  Declare Custom Entry term.

  Notation "[ e ]" := e (e custom term at level 2).
  Notation "( x )" := x (in custom term, x at level 2).

  Notation "'true'"  := (T_true)  (in custom term at level 0).
  Notation "'false'" := (T_false) (in custom term at level 0).

  Notation "'if' cond 'then' t1 'else' t2" :=
    (T_cond cond t1 t2) (in custom term at level 2).

  Notation "x" := x (in custom term at level 0, x constr at level 0).

  Check [ true ].
  Check fun cond t1 t2 => [ if cond then t1 else t2 ].
  Unset Printing Notations.
  Check fun cond t1 t2 => [ if cond then t1 else t2 ].
  Set Printing Notations.

  (* Evaluation relation on terms *)
  Reserved Notation "t ==> t'" (at level 50).

  Inductive eval_step : term -> term -> Prop :=
  | E_IfTrue  : forall t1 t2, [ if true  then t1 else t2 ] ==> t1
  | E_IfFalse : forall t1 t2, [ if false then t1 else t2 ] ==> t2
  | E_If : forall c c' t1 t2, c ==> c' -> [ if c then t1 else t2] ==> [ if c' then t1 else t2 ]
  where "e ==> e'" := (eval_step e e').

  Theorem ex_inst_e_iftrue :
    [ if true then true else (if false then false else false) ] ==> [ true ].
  Proof.
    by apply: E_IfTrue.
  Qed.

  Module Ex_3_5_3.
    Definition s := [ if true  then false else false ].
    Definition t := [ if s     then true  else true  ].
    Definition u := [ if false then true  else true  ].

    Theorem ex :
      [ if t then false else false ] ==> [ if u then false else false ].
    Proof.
      apply: E_If.
                     (*              t ==> u
         [ if s then true else true  ] ==> [ if false then true else true  ] *)
      apply: E_If.
      (*                                 s ==> [ false ]
         [ if true then false else false ] ==> [ false ] *)
      exact: E_IfTrue.

      (* Let's refactor it a bit *)
      Restart.

      by do 2! apply: E_If; exact: E_IfTrue.
    Qed.
  End Ex_3_5_3.

  Theorem eval_step_is_det :
    forall t t' t'' : term,
      (t ==> t') /\ (t ==> t'') -> t' = t''.
  Proof.
  (* I haven’t came up with a proof yet *)
  Abort.

  (* It would be much easier to define the
     one-step evaluation as a function instead: *)

  Fixpoint one_step (t : term) : term :=
    match t with
    | T_cond T_true t1 t2 => t1
    | T_cond T_false t1 t2 => t2
    | T_cond cond t1 t2 => T_cond (one_step cond) t1 t2
    | t => t
    end.

  (* A separate notation, now for the
     fixpoint-definition of one-step evaluation: *)

  Notation "t ==>> t'" := (one_step t = t') (at level 50).

  Theorem one_step_is_det t t' t'':
    t ==>> t' /\ t ==>> t'' -> t' = t''.
  Proof.
    case.
    move=> H1 H2.
    rewrite -H1 -H2.
    done.

    Restart.

    (* Idiomatic proof *)
    by move=> [] ->.
  Qed.

  Definition nf t := t ==>> t.

  Notation "| t |" := (nf t) (at level 200).

  (* Theorem 3.5.7:
     Every value is in normal form. *)

  Theorem vnf : |[[ true ]]| /\ |[[ false ]]|.
  Proof. by []. Qed.

  (* Theorem 3.5.8:
     If [t] is in normal form, then [t] is a value. *)

  Lemma nf_implies_not_cond v : forall c t1 t2,
    |v| -> v <> [[ if c then t1 else t2 ]].
  Proof.
    elim: v=> //= v H1 t H2 t' H3 cond' t1 t2 H.
  Abort.

  Theorem nf_implies_v v :
    nf v -> v = [[ true ]] \/ v = [[ false ]].
  Proof.
    case: v=> t.
    - by left.
    - by right.
    - move=> t1 t2.
      rewrite /nf.
  Abort.

  (* Тут могут пригодиться леммы типа такой --
     Lemma foo c t1 t2 : t1 <> T_cond c t1 t2. *)

End Ch3.
