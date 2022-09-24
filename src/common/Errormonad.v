From compcert Require Export Errors.
From vericert Require Import Monad.
From Coq Require Import Lists.List.

Module ErrorMonad <: Monad.

  Definition mon := res.

  Definition ret {A: Type} (x: A) := OK x.

  Definition default {T : Type} (x : T) (u : res T) : T :=
    match u with
    | OK y => y
    | _ => x
    end.

  Definition map {S : Type} {T : Type} (f : S -> T) (u : mon S) : mon T :=
    match u with
    | OK y => OK (f y)
    | Error m => Error m
    end.

  Definition liftA2 {T : Type} (f : T -> T -> T) (a : mon T) (b : mon T) : mon T :=
    match a with
    | OK x => map (f x) b
    | Error m => Error m
    end.

  Definition bind {A B : Type} (f : mon A) (g : A -> mon B) : mon B :=
    match f with
    | OK a => g a
    | Error m => Error m
    end.

  Definition bind2 {A B C : Type} (f : mon (A * B)) (g : A -> B -> mon C) : mon C :=
    match f with
    | OK (a, b) => g a b
    | Error m => Error m
    end.

  Definition join {A : Type} (a : mon (mon A)) : mon A :=
    match a with
    | Error m => Error m
    | OK a' => a'
    end.

End ErrorMonad.

Module ErrorMonadExtra := MonadExtra(ErrorMonad).
