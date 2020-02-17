(* 
 * CoqUp: Verified high-level synthesis.
 * Copyright (C) 2019-2020 Yann Herklotz <yann@yannherklotz.com>
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

From Coq Require Import
    Strings.String
    Bool.Bool
    Arith.Arith.

Local Open Scope string.

Module Show.
  Class Show A : Type :=
    {
      show : A -> string
    }.

  Instance showBool : Show bool :=
    {
      show := fun b:bool => if b then "true" else "false"
    }.

  Fixpoint string_of_nat_aux (time n : nat) (acc : string) : string :=
    let d := match n mod 10 with
             | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4" | 5 => "5"
             | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
             end in
    let acc' := d ++ acc in
    match time with
    | 0 => acc'
    | S time' =>
      match n / 10 with
      | 0 => acc'
      | n' => string_of_nat_aux time' n' acc'
      end
    end.

  Definition string_of_nat (n : nat) : string :=
    string_of_nat_aux n n "".

  Instance showNat : Show nat :=
    {
      show := string_of_nat
    }.

End Show.
Export Show.
