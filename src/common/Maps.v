From coqup Require Import Coquplib.

From compcert Require Export Maps.
From compcert Require Import Errors.
Import PTree.

Set Implicit Arguments.

Local Open Scope error_monad_scope.

(** Instance of traverse for [PTree] and [Errors]. This should maybe be generalised
    in the future. *)

Module PTree.

Fixpoint xtraverse (A B : Type) (f : positive -> A -> res B) (m : PTree.t A) (i : positive)
         {struct m} : res (PTree.t B) :=
  match m with
  | Leaf => OK Leaf
  | Node l o r =>
    let newo :=
        match o with
        | None => OK None
        | Some x =>
          match f (prev i) x with
          | Error err => Error err
          | OK val => OK (Some val)
          end
        end in
    match newo with
    | OK no =>
      do nl <- xtraverse f l (xO i);
      do nr <- xtraverse f r (xI i);
      OK (Node nl no nr)
    | Error msg => Error msg
    end
  end.

Definition traverse (A B : Type) (f : positive -> A -> res B) m := xtraverse f m xH.

Definition traverse1 (A B : Type) (f : A -> res B) := traverse (fun _ => f).

End PTree.
