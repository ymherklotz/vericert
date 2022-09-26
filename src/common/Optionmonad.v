(*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2022 Yann Herklotz <yann@yannherklotz.com>
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <https://www.gnu.org/licenses/>.
 *)

From vericert Require Import Monad.
From Coq Require Import Lists.List.

Module Option <: Monad.

  Definition mon := option.

  Definition ret {A: Type} (x: A) := Some x.

  Definition default {T : Type} (x : T) (u : option T) : T :=
    match u with
    | Some y => y
    | _ => x
    end.

  Definition map {S : Type} {T : Type} (f : S -> T) (u : option S) : option T :=
    match u with
    | Some y => Some (f y)
    | _ => None
    end.

  Definition liftA2 {T : Type} (f : T -> T -> T) (a : option T) (b : option T) : option T :=
    match a with
    | Some x => map (f x) b
    | _ => None
    end.

  Definition bind {A B : Type} (g : A -> option B) (f : option A) : option B :=
    match f with
    | Some a => g a
    | _ => None
    end.

  Definition bind2 {A B C : Type} (g : A -> B -> option C) (f : mon (A * B)) : option C :=
    match f with
    | Some (a, b) => g a b
    | _ => None
    end.

  Definition join {A : Type} (a : option (option A)) : option A :=
    match a with
    | None => None
    | Some a' => a'
    end.

  #[global] Instance option_ret : MRet option := @ret.
  #[global] Instance option_bind : MBind option := @bind.
  #[global] Instance option_join : MJoin option := @join.
  #[global] Instance option_map : FMap option := @map.
  #[global] Instance option_omap : OMap option := @bind.

End Option.

Module OptionExtra.
  Module OE := MonadExtra(Option).
  Export OE.

  Lemma mfold_left_Some :
    forall A B f x n y,
      @mfold_left A B f x n = Some y ->
      exists n', n = Some n'.
  Proof. induction x; intros; destruct n; eauto. Qed.

End OptionExtra.
