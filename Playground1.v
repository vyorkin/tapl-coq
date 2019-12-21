Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From mathcomp Require Import ssreflect ssrfun ssrbool.

Module Bool.
  Inductive bool : Type :=
  | true
  | false.

  Check true : bool.
  Check true.

  (* Gallina (курица (по-исп.)),
     e.g. "Gallina blanca" -- белая курица *)
  Definition idb := fun b : bool => b.

  Check (fun b : bool => b).

  Definition negb (b : bool) :=
    match b with
    | true => false
    | false => true
    end.

  Compute (negb false).

  Variable c : bool.

  Compute idb c.
  Compute (negb c).

  Definition andb (b c : bool) : bool :=
    match b with
    | true => c
    | false => false
    end.

  Compute andb c true.
  Compute andb c false.

  Definition twoVthreee (b : bool) :=
    match b with
    | true  => 2
    | flase => 3
    end.

  Eval compute in twoVthreee true.
  Eval compute in twoVthreee false.

End Bool.

Module Nat.
  Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

  (* struct n -- structural recursion on parameter n *)

  (* doesn't work, coq is unable to guess that (S n') is
  "structurally smaller" than n *)

  (* Fixpoint addn' (n m : nat) { struct n } : nat := *)
  (*   match n with *)
  (*   | S (S n') => S (S (addn' (S n') m)) *)
  (*   | S O => S m *)
  (*   | O => m *)
  (*   end. *)

  (* to make it work we should use an alias for (S n') -- Sn' *)

  Fixpoint addn (n m : nat) { struct n } : nat :=
    match n with
    | S (S n' as Sn') => S (S (addn Sn' m))
    | S O => S m
    | O => m
    end.

End Nat.

Module Props.
  Inductive False : Prop := .

  Print False.

  Fail Fixpoint loop (n : nat) : False := loop n.
  Fail Check (loop 0 : False).

  About nat.
  About S.

  Locate ".+1".
  (* Notation "n .+1" := (S n). *)

  (* Notations can not be partially applied *)

  Section Applyn.
    Variable f : nat -> nat.
    Fixpoint applyn (n : nat) (x : nat) : nat :=
      if n is (S n') then applyn n' (f x)
      else x.

    Compute (applyn (S (S O)) O).
    Compute (applyn 42 0).
    Print applyn.
    Check applyn.
    About applyn.
  End Applyn.

End Props.

Module Definitions.
  Eval compute in
    let n := 33 : nat in
    let e := n + n + n in
    e + e + e.

End Definitions.

Module CaseAnalysis.
  Inductive term : Type :=
  | foo
  | bar.

  Inductive step : term -> term -> Prop :=
  | Step1 : step foo bar
  | Step2 : step bar foo.

  Lemma ind_lem : forall t t' t'' : term,
      step t t' -> step t t'' -> t' = t''.
  Proof.
    move=> t t' t''.
    case.

    (* Вот то, что сделал case. выше: *)

    (* step foo t'' -> bar = t'' *)
    (* step bar t'' -> foo = t'' *)

    (* Вот то, что я раньше ошибочно думал, что он сделает: *)

    (* step foo t' -> step foo t'' -> t' = t''. *)
    (* step bar t' -> step bar t'' -> t' = t''. *)

    (* Вместо этого там (как я понимаю) на самом деле как бы: *)

    (* step foo bar -> step foo t'' -> bar = t''. *)
    (* step bar foo -> step bar t'' -> foo = t''. *)

    (* Только без головных этих предпосылок, которые я ошибочно,
       почему-то, ожидал увидеть, хотя в этом нет никакого смысла,
       тк это посылки в голове и есть именно те "случаи", которые
       разбирает case.
       (Все возможные конструкторы моего утверждения step t t')
     *)

    (* step foo bar -> step foo t'' -> t' = t''. *)
    (* step bar foo -> step bar t'' -> t' = t''. *)

    (* step foo bar -> step foo t'' -> bar = t''. *)
    (* step bar foo -> step bar t'' -> foo = t''. *)
    case.
  Abort.

End CaseAnalysis.
