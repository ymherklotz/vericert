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

#[local] Open Scope positive.

Record divider (signed: bool) : Type :=
  mk_divider {
    div_stages: positive;
    div_size: positive;
    div_numer: reg;
    div_denom: reg;
    div_quot: reg;
    div_rem: reg;
    div_ordering: (div_numer < div_denom
                  /\ div_denom < div_quot
                  /\ div_quot < div_rem)
  }.

Arguments div_stages [signed].
Arguments div_size [signed].
Arguments div_numer [signed].
Arguments div_denom [signed].
Arguments div_quot [signed].
Arguments div_rem [signed].

Record ram := mk_ram {
  ram_size: nat;
  ram_mem: reg;
  ram_en: reg;
  ram_u_en: reg;
  ram_addr: reg;
  ram_wr_en: reg;
  ram_d_in: reg;
  ram_d_out: reg;
  ram_ordering: (ram_addr < ram_en
                 /\ ram_en < ram_d_in
                 /\ ram_d_in < ram_d_out
                 /\ ram_d_out < ram_wr_en
                 /\ ram_wr_en < ram_u_en)
}.

Inductive funct_unit: Type :=
| SignedDiv: divider true -> funct_unit
| UnsignedDiv: divider false -> funct_unit
| Ram: ram -> funct_unit.

Definition funct_units := PTree.t funct_unit.

Record arch := mk_arch {
  arch_div: list positive;
  arch_sdiv: list positive;
  arch_ram: list positive;
}.

Record resources := mk_resources {
  res_funct_units: funct_units;
  res_arch: arch;
}.

Definition initial_funct_units: funct_units := PTree.empty _.

Definition initial_arch := mk_arch nil nil nil.

Definition initial_resources :=
  mk_resources initial_funct_units initial_arch.

Definition funct_unit_stages (f: funct_unit) : positive :=
  match f with
  | SignedDiv d => div_stages d
  | UnsignedDiv d => div_stages d
  | _ => 1
  end.
