(*
 * CoqUp: Verified high-level synthesis.
 * Copyright (C) 2020 Yann Herklotz <yann@yannherklotz.com>
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

From Coq Require Import FSets.FMapPositive.
From compcert Require RTL Op Maps.
From coqup Require Import Coquplib Verilog Veriloggen Value.

(** * Relational specification of the translation *)

(** We now define inductive predicates that characterise the fact that the
statemachine that is created by the translation contains the correct
translations for each of the elements *)

Inductive tr_op : Op.operation -> list reg -> expr -> Prop :=
| tr_op_Omove : forall r, tr_op Op.Omove (r::nil) (Vvar r)
| tr_op_Ointconst : forall n l, tr_op (Op.Ointconst n) l (Vlit (intToValue n))
| tr_op_Oneg : forall r, tr_op Op.Oneg (r::nil) (Vunop Vneg (Vvar r))
| tr_op_Osub : forall r1 r2, tr_op Op.Osub (r1::r2::nil) (bop Vsub r1 r2)
| tr_op_Omul : forall r1 r2, tr_op Op.Omul (r1::r2::nil) (bop Vmul r1 r2)
| tr_op_Omulimm : forall r n, tr_op (Op.Omulimm n) (r::nil) (boplit Vmul r n)
| tr_op_Odiv : forall r1 r2, tr_op Op.Odiv (r1::r2::nil) (bop Vdiv r1 r2)
| tr_op_Odivu : forall r1 r2, tr_op Op.Odivu (r1::r2::nil) (bop Vdivu r1 r2)
| tr_op_Omod : forall r1 r2, tr_op Op.Omod (r1::r2::nil) (bop Vmod r1 r2)
| tr_op_Omodu : forall r1 r2, tr_op Op.Omodu (r1::r2::nil) (bop Vmodu r1 r2)
| tr_op_Oand : forall r1 r2, tr_op Op.Oand (r1::r2::nil) (bop Vand r1 r2)
| tr_op_Oandimm : forall n r, tr_op (Op.Oandimm n) (r::nil) (boplit Vand r n)
| tr_op_Oor : forall r1 r2, tr_op Op.Oor (r1::r2::nil) (bop Vor r1 r2)
| tr_op_Oorimm : forall n r, tr_op (Op.Oorimm n) (r::nil) (boplit Vor r n)
| tr_op_Oxor : forall r1 r2, tr_op Op.Oxor (r1::r2::nil) (bop Vxor r1 r2)
| tr_op_Oxorimm : forall n r, tr_op (Op.Oxorimm n) (r::nil) (boplit Vxor r n)
| tr_op_Onot : forall r, tr_op Op.Onot (r::nil) (Vunop Vnot (Vvar r))
| tr_op_Oshl : forall r1 r2, tr_op Op.Oshl (r1::r2::nil) (bop Vshl r1 r2)
| tr_op_Oshlimm : forall n r, tr_op (Op.Oshlimm n) (r::nil) (boplit Vshl r n)
| tr_op_Oshr : forall r1 r2, tr_op Op.Oshr (r1::r2::nil) (bop Vshr r1 r2)
| tr_op_Oshrimm : forall n r, tr_op (Op.Oshrimm n) (r::nil) (boplit Vshr r n)
| tr_op_Ocmp : forall c l e s s' i, translate_condition c l s = OK e s' i -> tr_op (Op.Ocmp c) l e
| tr_op_Olea : forall a l e s s' i, translate_eff_addressing a l s = OK e s' i -> tr_op (Op.Olea a) l e.

Inductive tr_instr (fin rtrn st : reg) : RTL.instruction -> stmnt -> stmnt -> Prop :=
| tr_instr_Inop :
    forall n,
      tr_instr fin rtrn st (RTL.Inop n) Vskip (state_goto st n)
| tr_instr_Iop :
    forall n op args e dst,
      tr_op op args e ->
      tr_instr fin rtrn st (RTL.Iop op args dst n) (Vnonblock (Vvar dst) e) (state_goto st n)
| tr_instr_Icond :
    forall n1 n2 cond args s s' i c,
      translate_condition cond args s = OK c s' i ->
      tr_instr fin rtrn st (RTL.Icond cond args n1 n2) Vskip (state_cond st c n1 n2)
| tr_instr_Ireturn_None :
      tr_instr fin rtrn st (RTL.Ireturn None) (block fin (Vlit (ZToValue 1%nat 1%Z))) Vskip
| tr_instr_Ireturn_Some :
    forall r,
      tr_instr fin rtrn st (RTL.Ireturn (Some r))
               (Vseq (block fin (Vlit (ZToValue 1%nat 1%Z))) (block rtrn (Vvar r))) Vskip.

Inductive tr_code (c : RTL.code) (stmnts trans : PositiveMap.t stmnt)
          (fin rtrn st : reg) : Prop :=
| tr_code_intro :
    forall i s t n,
      Maps.PTree.get n c = Some i ->
      stmnts!n = Some s ->
      trans!n = Some t ->
      tr_instr fin rtrn st i s t ->
      tr_code c stmnts trans fin rtrn st.

(** [tr_module_items start clk st rst s mis] holds if the state is correctly
translated to actual Verilog, meaning it is correctly implemented as a state
machine in Verilog.  Currently it does not seem that useful because it models
the [make_module_items] nearly exactly.  Therefore it might have to be changed
to make up for that. *)

Inductive tr_module_items : node -> reg -> reg -> reg -> state -> list module_item -> Prop :=
  tr_module_items_intro :
    forall start clk st rst s mis,
      Valways_ff (Vposedge clk)
                 (Vcond (Vbinop Veq (Vinputvar rst) (Vlit (ZToValue 1 1)))
                        (nonblock st (posToExpr 32 start))
                        (make_statetrans st s.(st_statetrans)))
      :: Valways_ff (Vposedge clk) (make_stm st s.(st_stm))
      :: List.map allocate_reg (PositiveMap.elements s.(st_decl)) = mis ->
      tr_module_items start clk st rst s mis.

(** [tr_module function module] Holds if the [module] is the correct translation
of the [function] that it was given. *)

Inductive tr_module : RTL.function -> module -> Prop :=
  tr_module_intro :
    forall f mi st rtrn fin clk rst start s0 s1 s2 s3 s4 s5 s6 i1 i2 i3 i4 i5 i6,
      decl_io 1 s0 = OK fin s1 i1 ->
      decl_io 32 s1 = OK rtrn s2 i2 ->
      decl_io 1 s2 = OK start s3 i3 ->
      decl_io 1 s3 = OK rst s4 i4 ->
      decl_io 1 s4 = OK clk s5 i5 ->
      decl_fresh_reg 32 s5 = OK st s6 i6 ->
      tr_code f.(RTL.fn_code) s6.(st_stm)
                                   (PositiveMap.map (statetrans_transl (fst st)) s6.(st_statetrans))
                                   (fst fin) (fst rtrn) (fst st) ->
      tr_module_items f.(RTL.fn_entrypoint) (fst clk) (fst st) (fst rst) s6 mi ->
      tr_module f (mkmodule
                     start
                     rst
                     clk
                     fin
                     rtrn
                     st
                     (List.map set_int_size f.(RTL.fn_params))
                     mi).

Lemma tr_module_correct:
  forall f m,
  transl_module f = Errors.OK m ->
  tr_module f m.
Admitted.
