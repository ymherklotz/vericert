(*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2021 Yann Herklotz <yann@yannherklotz.com>
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

Require Import compcert.backend.Registers.
Require Import compcert.lib.Maps.

Require Import vericert.common.Vericertlib.

Inductive funct_unit: Type :=
| SignedDiv (size: positive) (numer denom quot rem: reg): funct_unit
| UnsignedDiv (size: positive) (numer denom quot rem: reg): funct_unit.

Record funct_units := mk_avail_funct_units {
    avail_sdiv: option positive;
    avail_udiv: option positive;
    avail_units: PTree.t funct_unit;
  }.

Definition initial_funct_units :=
  mk_avail_funct_units None None (PTree.empty funct_unit).

Definition funct_unit_stages (f: funct_unit) : positive :=
  match f with
  | SignedDiv s _ _ _ _ => s
  | UnsignedDiv s _ _ _ _ => s
  end.
