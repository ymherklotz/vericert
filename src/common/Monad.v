From Coq Require Import Lists.List.

Module Type Monad.

  Parameter mon : Type -> Type.

  Parameter ret : forall (A : Type) (x : A), mon A.
  Arguments ret [A].

  Parameter bind : forall (A B : Type) (f : mon A) (g : A -> mon B), mon B.
  Arguments bind [A B].

  Parameter bind2 : forall (A B C: Type) (f: mon (A * B)) (g: A -> B -> mon C), mon C.
  Arguments bind2 [A B C].

End Monad.

Module MonadExtra(M : Monad).
  Import M.

  Module MonadNotation.

    Notation "'do' X <- A ; B" :=
      (bind A (fun X => B))
        (at level 200, X ident, A at level 100, B at level 200).
    Notation "'do' ( X , Y ) <- A ; B" :=
      (bind2 A (fun X Y => B))
        (at level 200, X ident, Y ident, A at level 100, B at level 200).

  End MonadNotation.
  Import MonadNotation.

  Fixpoint sequence {A: Type} (l: list (mon A)) {struct l}: mon (list A) :=
    match l with
    | nil => ret nil
    | x::xs =>
      do r <- x;
      do rs <- sequence xs;
      ret (r::rs)
    end.

  Fixpoint traverselist {A B: Type} (f: A -> mon B) (l: list A) {struct l}: mon (list B) :=
    sequence (map f l).

  Fixpoint traverseoption {A B: Type} (f: A -> mon B) (opt: option A) {struct opt}: mon (option B) :=
    match opt with
    | None => ret None
    | Some x =>
      do r <- f x;
      ret (Some r)
    end.

  Fixpoint collectlist {A : Type} (f : A -> mon unit) (l : list A) {struct l} : mon unit :=
    match l with
    | nil => ret tt
    | x::xs => do _ <- f x; collectlist f xs
    end.

End MonadExtra.
