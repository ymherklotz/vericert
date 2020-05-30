From compcert Require Errors.
From coqup Require Import Monad.
From Coq Require Import Lists.List.

Module Type State.
  Parameter st : Type.
  Parameter st_prop : st -> st -> Prop.

  Axiom st_refl : forall s, st_prop s s.
  Axiom st_trans : forall s1 s2 s3, st_prop s1 s2 -> st_prop s2 s3 -> st_prop s1 s3.
End State.

Module Statemonad(S : State) <: Monad.

  Inductive res (A: Type) (s: S.st): Type :=
  | Error : Errors.errmsg -> res A s
  | OK : A -> forall (s' : S.st), S.st_prop s s' -> res A s.

  Arguments OK [A s].
  Arguments Error [A s].

  Definition mon (A: Type) : Type := forall (s: S.st), res A s.

  Definition ret {A: Type} (x: A) : mon A :=
    fun (s : S.st) => OK x s (S.st_refl s).

  Definition bind {A B: Type} (f: mon A) (g: A -> mon B) : mon B :=
    fun (s : S.st) =>
      match f s with
      | Error msg => Error msg
      | OK a s' i =>
        match g a s' with
        | Error msg => Error msg
        | OK b s'' i' => OK b s'' (S.st_trans s s' s'' i i')
        end
      end.

  Definition bind2 {A B C: Type} (f: mon (A * B)) (g: A -> B -> mon C) : mon C :=
    bind f (fun xy => g (fst xy) (snd xy)).

  Definition handle_error {A: Type} (f g: mon A) : mon A :=
    fun (s : S.st) =>
      match f s with
      | OK a s' i => OK a s' i
      | Error _ => g s
      end.

  Definition error {A: Type} (err: Errors.errmsg) : mon A := fun (s: S.st) => Error err.

  Definition get : mon S.st := fun s => OK s s (S.st_refl s).

  Definition set (s: S.st) (i: forall s', S.st_prop  s' s) : mon unit :=
    fun s' => OK tt s (i s').

  Definition run_mon {A: Type} (s: S.st) (m: mon A): Errors.res A :=
    match m s with
    | OK a s' i => Errors.OK a
    | Error err => Errors.Error err
    end.

End Statemonad.
