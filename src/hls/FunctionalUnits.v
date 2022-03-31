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
}.

Definition all_ram_regs r :=
  ram_mem r::ram_en r::ram_u_en r::ram_addr r::ram_wr_en r::ram_d_in r::ram_d_out r::nil.

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

Definition index_div {b:bool} r (d: divider b) :=
  match r with
  | 1 => div_numer d
  | 2 => div_denom d
  | 3 => div_quot d
  | _ => div_rem d
  end.

Definition index_ram r (d: ram) :=
  match r with
  | 1 => ram_mem d
  | 2 => ram_en d
  | 3 => ram_u_en d
  | 4 => ram_addr d
  | 5 => ram_wr_en d
  | 6 => ram_d_in d
  | _ => ram_d_out d
  end.

Definition index_res u r res :=
  match PTree.get u res with
  | Some (SignedDiv d) => Some (index_div r d)
  | Some (UnsignedDiv d) => Some (index_div r d)
  | Some (Ram d) => Some (index_ram r d)
  | None => None
  end.

Definition get_ram n res: option (positive * ram) :=
  match nth_error (arch_ram (res_arch res)) n with
  | Some ri =>
      match PTree.get ri (res_funct_units res) with
      | Some (Ram r) => Some (ri, r)
      | _ => None
      end
  | None => None
  end.

Definition get_div n res :=
  match nth_error (arch_div (res_arch res)) n with
  | Some ri =>
      match PTree.get ri (res_funct_units res) with
      | Some (UnsignedDiv d) => Some (ri, d)
      | _ => None
      end
  | None => None
  end.

Definition get_sdiv n res :=
  match nth_error (arch_sdiv (res_arch res)) n with
  | Some ri =>
      match PTree.get ri (res_funct_units res) with
      | Some (SignedDiv d) => Some (ri, d)
      | _ => None
      end
  | None => None
  end.

Definition set_res fu res :=
  let max := ((fold_left Pos.max ((arch_sdiv (res_arch res))
                                  ++ (arch_div (res_arch res))
                                  ++ (arch_ram (res_arch res))) 1) + 1)%positive in
  let nt := PTree.set max fu (res_funct_units res) in
  match fu with
  | UnsignedDiv _ => mk_resources nt (mk_arch (max :: arch_div (res_arch res))
                                              (arch_sdiv (res_arch res))
                                              (arch_ram (res_arch res)))
  | SignedDiv _ => mk_resources nt (mk_arch (arch_div (res_arch res))
                                            (max :: arch_sdiv (res_arch res))
                                            (arch_ram (res_arch res)))
  | Ram _ => mk_resources nt (mk_arch (arch_div (res_arch res))
                                      (arch_sdiv (res_arch res))
                                      (max :: arch_ram (res_arch res)))
  end.

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

Definition max_reg_ram r :=
  fold_right Pos.max 1 (ram_mem r::ram_en r::ram_u_en r::ram_addr r
                                ::ram_wr_en r::ram_d_in r::ram_d_out r::nil).

Definition max_reg_divider {b: bool} (d: divider b) :=
  fold_right Pos.max 1 (div_numer d::div_denom d::div_quot d::div_rem d::nil).

Definition max_reg_fu fu :=
  match fu with
  | SignedDiv d | UnsignedDiv d => max_reg_divider d
  | Ram r => max_reg_ram r
  end.

Definition max_reg_funct_units r :=
  PTree.fold (fun m _ a => Pos.max m (max_reg_fu a)) r 1.

Definition max_reg_resources r :=
  max_reg_funct_units r.(res_funct_units).
