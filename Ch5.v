Set Implicit Arguments.

From Coq Require Import ssreflect.

Module Ch5.
  (* I recommend using pLam (https://github.com/slovnicki/pLam) *)
  (* to play around with pure λ-calculus  *)

  (* T = \t. \f. t = \t f. t *)
  (* F = \t. \f. f = \t f. f *)

  (* test = \c t f. c t f *)

  (* test T v w *)
  (* #0: ((((λc. (λt. (λf. ((c t) f)))) T) v) w) *)
  (* #1: (((λt. (λf. ((T t) f))) v) w) *)
  (* #2: ((λf. ((T v) f)) w) *)
  (* #3: (((λx. (λy. x)) v) w) *)
  (* #4: ((λy. v) w) *)
  (* #5: v *)

  (* and = \x y. x y F *)

  (* and T T *)
  (* #0: (((λx. (λy. ((x y) F))) T) T) *)
  (* #1: ((λy. ((T y) F)) T) *)
  (* #1: ((T T) F) *)
  (* #2: (((λx. (λy. x)) T) F) *)
  (* #3: ((λy. T) F) *)
  (* #4: T *)

  (* and T F *)
  (* #0: (((λx. (λy. ((x y) F))) T) F) *)
  (* #1: ((λy. ((T y) F)) F) *)
  (* #2: (((λx. (λy. x)) F) F) *)
  (* #3: ((λy. F) F) *)
  (* #4: F *)

  (* or = \x y. x T y *)

  (* or T T *)
  (* #0: (((λx. (λy. ((x T) y))) T) T) *)
  (* #1: ((λy. ((T T) y)) T) *)
  (* #2: (((λx. (λy. x)) T) T) *)
  (* #3: ((λy. T) T) *)
  (* #4: T *)

  (* or T F *)
  (* #0: (((λx. (λy. ((x T) y))) T) F) *)
  (* #1: ((λy. ((T T) y)) F) *)
  (* #2: (((λx. (λy. x)) T) F) *)
  (* #3: ((λy. T) F) *)
  (* #4: T *)

  (* not = \x. x F T *)

  (* not T *)
  (* #0: ((λx. ((x F) T)) T) *)
  (* #1: (((λx. (λy. x)) F) T) *)
  (* #2: ((λy. F) T) *)
  (* #3: F *)

  (* not F *)
  (* #0: ((λx. ((x F) T)) F) *)
  (* #1: (((λx. (λy. y)) F) T) *)
  (* #2: ((λy. y) T) *)
  (* #3: T *)

  (* pair = \f s b. b f s *)
  (* fst  = \p. p T *)
  (* snd  = \p. p F *)

  (* fst (pair x y) *)
  (* #0: ((λp. (p T)) ((pair x) y)) *)
  (* #1: ((((λf. (λs. (λb. ((b f) s)))) x) y) T) *)
  (* #2: (((λs. (λb. ((b x) s))) y) T) *)
  (* #3: ((λb. ((b x) y)) T) *)
  (* #4: (((λx. (λy. x)) x) y) *)
  (* #5: ((λy. x) y) *)
  (* #6: x *)

End Ch5.
