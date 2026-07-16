From Stdlib Require Import List String.
Import ListNotations.

Inductive error : Set :=
  | E_msg              (msg : string)
  | E_unsupported      (what : string)
  | E_invalid_type     (msg : string)
  | E_invalid_value    (msg : string)
  | E_multiply_defined (name : string)
  | E_bad_identifier   (name : string).

Declare Scope result_scope.
Delimit Scope result_scope with res.
Local Open Scope result_scope.

Definition result A := result A error.

Notation "'return' x" := (Ok x) (at level 60) : result_scope.
Notation "'fail' x" := (Error x) (at level 60) : result_scope.

Notation " x <- e1 ;; e2" := (match e1 with
                              | Ok x => e2
                              | Error err => Error err
                              end) (right associativity, at level 60) : result_scope.

Notation "'_' <- e1 ;; e2" := (match e1 with
                               | Ok _ => e2
                               | Error err => Error err
                               end) (right associativity, at level 60) : result_scope.

Notation "'assert' b ! e1 ;; e2" := (if b then e2 else Error e1) (at level 60) : result_scope.

(* Map a fallible function across a list *)
Fixpoint mapM {A B} (f : A -> result B) (xs : list A) : result (list B) :=
  match xs with
  | [] => Ok []
  | x :: xs' =>
      match f x with
      | Error e => Error e
      | Ok y =>
          match mapM f xs' with
          | Error e => Error e
          | Ok ys => Ok (y :: ys)
          end
      end
  end.

Fixpoint good_list {A} (l : list (result A)) : result (list A) :=
  match l with
  | [] => Ok []
  | Error e :: _ => Error e
  | Ok x :: xs' =>
      tl <- good_list xs';;
      Ok (x :: tl)
  end.

Tactic Notation "mdestruct" "in" hyp(H) :=
  lazymatch type of H with
  | context[_ <- ?x ;; _] =>
      let E := fresh "E" in destruct x eqn:E in H;
      try solve [inversion H]
  | context[assert ?b ! _ ;; _] =>
      let E := fresh "E" in destruct b eqn:E in H;
      try solve [inversion H]
  | context[return _ = return ?x] => inversion H; subst x; clear H
  | context[fail _ = return _] => solve [inversion H]
  end.
