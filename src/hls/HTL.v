(*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2020 Yann Herklotz <yann@yannherklotz.com>
 *               2020 James Pollard <j@mes.dev>
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

Require Import Coq.FSets.FMapPositive.
Require Import Coq.micromega.Lia.

Require compcert.common.Events.
Require compcert.common.Globalenvs.
Require compcert.common.Smallstep.
Require compcert.common.Values.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.

Require Import vericert.common.Vericertlib.
Require Import vericert.hls.ValueInt.
Require Import vericert.hls.AssocMap.
Require Import vericert.hls.Array.
Require Import vericert.common.Maps.
Require vericert.hls.Verilog.

Local Open Scope positive.

(** The purpose of the hardware transfer language (HTL) is to create a more
hardware-like layout that is still similar to the register transfer language
(RTL) that it came from. The main change is that function calls become module
instantiations and that we now describe a state machine instead of a
control-flow graph. *)

Local Open Scope assocmap.

Definition reg := positive.
Definition node := positive.
Definition ident := positive.

Definition datapath_stmnt := Verilog.stmnt.
Definition datapath := PTree.t datapath_stmnt.
Definition control_stmnt := Verilog.stmnt.
Definition controllogic := PTree.t control_stmnt.

Definition map_well_formed {A : Type} (m : PTree.t A) : Prop :=
  forall p0 : positive,
    In p0 (map fst (Maps.PTree.elements m)) ->
    (Z.pos p0 <= Integers.Int.max_unsigned)%Z.

Definition ram_ordering a b c d e f := a < b < c /\ c < d < e /\ e < f.

Record ram := mk_ram {
  ram_size: nat;
  ram_mem: reg;
  ram_en: reg;
  ram_u_en: reg;
  ram_addr: reg;
  ram_wr_en: reg;
  ram_d_in: reg;
  ram_d_out: reg;
  ram_ordering_wf: ram_ordering ram_addr ram_en ram_d_in ram_d_out ram_wr_en ram_u_en
}.

Definition module_ordering a b c d e f g := a < b < c /\ c < d < e /\ e < f < g.

Inductive controlsignal : Type :=
  | ctrl_finish : controlsignal
  | ctrl_return : controlsignal
  | ctrl_start : controlsignal
  | ctrl_reset : controlsignal
  | ctrl_clk : controlsignal
  | ctrl_param (idx : nat) : controlsignal.

Definition controlsignal_sz (s : controlsignal) : nat :=
  match s with
  | ctrl_param _ => 32
  | ctrl_return => 32
  | _ => 1
  end.

Record module: Type :=
  mkmodule {
    mod_params : list reg;
    mod_datapath : datapath;
    mod_controllogic : controllogic;
    mod_entrypoint : node;
    mod_st : reg;
    mod_stk : reg;
    mod_stk_len : nat;
    mod_finish : reg;
    mod_return : reg;
    mod_start : reg;
    mod_reset : reg;
    mod_clk : reg;
    mod_scldecls : AssocMap.t (option Verilog.io * Verilog.scl_decl);
    mod_arrdecls : AssocMap.t (option Verilog.io * Verilog.arr_decl);
    (** Map from registers in this module to control registers in other modules.
        These will be mapped to the same verilog register. *)
    mod_externctrl : AssocMap.t (ident * controlsignal);
    mod_ram : option ram;
    mod_wf : map_well_formed mod_controllogic /\ map_well_formed mod_datapath;
    mod_ordering_wf : module_ordering mod_st mod_finish mod_return mod_stk mod_start mod_reset mod_clk;
    mod_ram_wf : forall r', mod_ram = Some r' -> mod_clk < ram_addr r';
    mod_params_wf : Forall (Pos.gt mod_st) mod_params;
  }.

Definition fundef := AST.fundef module.

Definition program := AST.program fundef unit.

Fixpoint init_regs (vl : list value) (rl : list reg) {struct rl} :=
  match rl, vl with
  | r :: rl', v :: vl' => AssocMap.set r v (init_regs vl' rl')
  | _, _ => empty_assocmap
  end.

Definition empty_stack (m : module) : Verilog.assocmap_arr :=
  (AssocMap.set m.(mod_stk) (Array.arr_repeat None m.(mod_stk_len)) (AssocMap.empty Verilog.arr)).


Definition prog_modmap (p : HTL.program) :=
  PTree_Properties.of_list (Option.map_option
                               (fun a => match a with
                                      | (ident, (AST.Gfun (AST.Internal f))) => Some (ident, f)
                                      | _ => None
                                      end)
                               (AST.prog_defs p)).

Lemma max_pc_wf :
  forall T m, (Z.pos (max_pc_map m) <= Integers.Int.max_unsigned)%Z ->
            @map_well_formed T m.
Proof.
  unfold map_well_formed. intros.
  exploit list_in_map_inv. eassumption. intros [x [A B]]. destruct x.
  apply Maps.PTree.elements_complete in B. apply max_pc_map_sound in B.
  unfold Ple in B. apply Pos2Z.pos_le_pos in B. subst.
  simplify. transitivity (Z.pos (max_pc_map m)); eauto.
Qed.

(** * Operational Semantics *)

Definition genv := Globalenvs.Genv.t fundef unit.

Definition find_func {F V} (ge : Globalenvs.Genv.t F V) (symb : AST.ident) : option F :=
  match Globalenvs.Genv.find_symbol ge symb with
  | None => None
  | Some b => Globalenvs.Genv.find_funct_ptr ge b
  end.

Inductive stackframe : Type :=
  Stackframe : forall (mid : ident)
                 (m : module)
                 (st : node)
                 (reg_assoc : Verilog.assocmap_reg)
                 (arr_assoc : Verilog.assocmap_arr),
    stackframe.

Inductive state : Type :=
| State :
    forall (stack : list stackframe)
           (mid : ident)
           (m : module)
           (st : node)
           (reg_assoc : Verilog.assocmap_reg)
           (arr_assoc : Verilog.assocmap_arr), state
| Returnstate :
    forall (res : list stackframe)
           (mid : ident) (** Name of the callee *)
           (v : value), state
| Callstate :
    forall (stack : list stackframe)
           (mid : ident)
           (m : module)
           (args : list value), state.

Inductive exec_ram:
  Verilog.reg_associations -> Verilog.arr_associations -> option ram ->
  Verilog.reg_associations -> Verilog.arr_associations -> Prop :=
| exec_ram_Some_idle:
    forall ra ar r,
      Int.eq (Verilog.assoc_blocking ra)#(ram_en r, 32)
             (Verilog.assoc_blocking ra)#(ram_u_en r, 32) = true ->
      exec_ram ra ar (Some r) ra ar
| exec_ram_Some_write:
    forall ra ar r d_in addr en wr_en u_en,
      Int.eq en u_en = false ->
      Int.eq wr_en (ZToValue 0) = false ->
      (Verilog.assoc_blocking ra)#(ram_en r, 32) = en ->
      (Verilog.assoc_blocking ra)!(ram_u_en r) = Some u_en ->
      (Verilog.assoc_blocking ra)!(ram_wr_en r) = Some wr_en ->
      (Verilog.assoc_blocking ra)!(ram_d_in r) = Some d_in ->
      (Verilog.assoc_blocking ra)!(ram_addr r) = Some addr ->
      exec_ram ra ar (Some r) (Verilog.nonblock_reg (ram_en r) ra u_en)
               (Verilog.nonblock_arr (ram_mem r) (valueToNat addr) ar d_in)
| exec_ram_Some_read:
    forall ra ar r addr v_d_out en u_en,
      Int.eq en u_en = false ->
      (Verilog.assoc_blocking ra)#(ram_en r, 32) = en ->
      (Verilog.assoc_blocking ra)!(ram_u_en r) = Some u_en ->
      (Verilog.assoc_blocking ra)!(ram_wr_en r) = Some (ZToValue 0) ->
      (Verilog.assoc_blocking ra)!(ram_addr r) = Some addr ->
      Verilog.arr_assocmap_lookup (Verilog.assoc_blocking ar)
                                  (ram_mem r) (valueToNat addr) = Some v_d_out ->
      exec_ram ra ar (Some r) (Verilog.nonblock_reg (ram_en r)
                               (Verilog.nonblock_reg (ram_d_out r) ra v_d_out) u_en) ar
| exec_ram_None:
    forall r a,
      exec_ram r a None r a.

Inductive step : genv -> state -> Events.trace -> state -> Prop :=
| step_module :
    forall g mid m st sf ctrl_stmnt data_stmnt
      asr asa
      basr1 basa1 nasr1 nasa1
      basr2 basa2 nasr2 nasa2
      basr3 basa3 nasr3 nasa3
      asr' asa'
      f pstval,
      asr!(mod_reset m) = Some (ZToValue 0) ->
      asr!(mod_finish m) = Some (ZToValue 0) ->
      asr!(m.(mod_st)) = Some (posToValue st) ->
      m.(mod_controllogic)!st = Some ctrl_stmnt ->
      m.(mod_datapath)!st = Some data_stmnt ->
      Verilog.stmnt_runp f
        (Verilog.mkassociations asr empty_assocmap)
        (Verilog.mkassociations asa (empty_stack m))
        ctrl_stmnt
        (Verilog.mkassociations basr1 nasr1)
        (Verilog.mkassociations basa1 nasa1) ->
      basr1!(m.(mod_st)) = Some (posToValue st) ->
      Verilog.stmnt_runp f
        (Verilog.mkassociations basr1 nasr1)
        (Verilog.mkassociations basa1 nasa1)
        data_stmnt
        (Verilog.mkassociations basr2 nasr2)
        (Verilog.mkassociations basa2 nasa2) ->
      exec_ram
        (Verilog.mkassociations (Verilog.merge_regs nasr2 basr2) empty_assocmap)
        (Verilog.mkassociations (Verilog.merge_arrs nasa2 basa2) (empty_stack m))
        (mod_ram m)
        (Verilog.mkassociations basr3 nasr3)
        (Verilog.mkassociations basa3 nasa3) ->
      asr' = Verilog.merge_regs nasr3 basr3 ->
      asa' = Verilog.merge_arrs nasa3 basa3 ->
      asr'!(m.(mod_st)) = Some (posToValue pstval) ->
      (Z.pos pstval <= Integers.Int.max_unsigned)%Z ->
      step g
           (State sf mid m st     asr  asa) Events.E0
           (State sf mid m pstval asr' asa')
| step_finish :
    forall g m st asr asa retval sf mid,
    asr!(m.(mod_finish)) = Some (ZToValue 1) ->
    asr!(m.(mod_return)) = Some retval ->

    step g
         (State sf mid m st asr asa) Events.E0
         (Returnstate sf mid retval)
| step_initcall :
    forall g callerid caller st asr asa sf callee_id callee callee_reset callee_params callee_param_vals,
    find_func g callee_id = Some (AST.Internal callee) ->

    caller.(mod_externctrl)!callee_reset = Some (callee_id, ctrl_reset) ->
    (forall n param, nth_error callee_params n = Some param ->
          caller.(mod_externctrl)!param = Some (callee_id, ctrl_param n)) ->

    (* The fact that this is the only condition on the current state to trigger
       a call introduces non-determinism into the semantics. The semantics
       permit initiating a call from any state where a reset has been set to 0.
     *)
    asr!callee_reset = Some (ZToValue 0) ->
    callee_param_vals = List.map (fun p => asr#p) callee_params ->

    step g
         (State sf callerid caller st asr asa) Events.E0
         (Callstate (Stackframe callerid caller st asr asa :: sf)
                    callee_id callee callee_param_vals)

| step_call :
    forall g mid m args res,
      step g
           (Callstate res mid m args) Events.E0
           (State res mid m m.(mod_entrypoint)
             (AssocMap.set (mod_reset m) (ZToValue 0)
              (AssocMap.set (mod_finish m) (ZToValue 0)
               (AssocMap.set (mod_st m) (posToValue m.(mod_entrypoint))
                (init_regs args m.(mod_params)))))
             (empty_stack m))

| step_return :
    forall g callerid caller asr asa callee_id callee_return callee_finish i sf pc mst,
      mst = mod_st caller ->

      caller.(mod_externctrl)!callee_return = Some (callee_id, ctrl_return) ->
      caller.(mod_externctrl)!callee_finish = Some (callee_id, ctrl_finish) ->

      step g
           (Returnstate (Stackframe callerid caller pc asr asa :: sf) callee_id i) Events.E0
           (State sf callerid caller pc
                  (asr # mst <- (posToValue pc) # callee_finish <- (ZToValue 1) # callee_return <- i)
                  asa).
Hint Constructors step : htl.

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b m0 m,
      let ge := Globalenvs.Genv.globalenv p in
      Globalenvs.Genv.init_mem p = Some m0 ->
      Globalenvs.Genv.find_symbol ge p.(AST.prog_main) = Some b ->
      Globalenvs.Genv.find_funct_ptr ge b = Some (AST.Internal m) ->
      initial_state p (Callstate nil p.(AST.prog_main) m nil).

Inductive final_state : state -> Integers.int -> Prop :=
| final_state_intro : forall retval mid retvali,
    retvali = valueToInt retval ->
    final_state (Returnstate nil mid retval) retvali.

Definition semantics (m : program) :=
  Smallstep.Semantics step (initial_state m) final_state
                      (Globalenvs.Genv.globalenv m).

Definition max_pc_function (m: module) :=
  List.fold_left Pos.max (List.map fst (PTree.elements m.(mod_controllogic))) 1.

Definition max_list := fold_right Pos.max 1.

Definition max_stmnt_tree t :=
  PTree.fold (fun i _ st => Pos.max (Verilog.max_reg_stmnt st) i) t 1.

Definition max_reg_ram r :=
  match r with
  | None => 1
  | Some ram => Pos.max (ram_mem ram)
                (Pos.max (ram_en ram)
                 (Pos.max (ram_addr ram)
                  (Pos.max (ram_addr ram)
                   (Pos.max (ram_wr_en ram)
                    (Pos.max (ram_d_in ram)
                     (Pos.max (ram_d_out ram) (ram_u_en ram)))))))
  end.

Definition max_reg_module m :=
  Pos.max (max_list (mod_params m))
   (Pos.max (max_stmnt_tree (mod_datapath m))
    (Pos.max (max_stmnt_tree (mod_controllogic m))
     (Pos.max (mod_st m)
      (Pos.max (mod_stk m)
       (Pos.max (mod_finish m)
        (Pos.max (mod_return m)
         (Pos.max (mod_start m)
          (Pos.max (mod_reset m)
           (Pos.max (mod_clk m) (max_reg_ram (mod_ram m))))))))))).

Lemma max_fold_lt :
  forall m l n, m <= n -> m <= (fold_left Pos.max l n).
Proof. induction l; crush; apply IHl; lia. Qed.

Lemma max_fold_lt2 :
  forall (l: list (positive * Verilog.stmnt)) v n,
    v <= n ->
    v <= fold_left (fun a p => Pos.max (Verilog.max_reg_stmnt (snd p)) a) l n.
Proof. induction l; crush; apply IHl; lia. Qed.

Lemma max_fold_lt3 :
  forall (l: list (positive * Verilog.stmnt)) v v',
    v <= v' ->
    fold_left (fun a0 p => Pos.max (Verilog.max_reg_stmnt (snd p)) a0) l v
    <= fold_left (fun a0 p => Pos.max (Verilog.max_reg_stmnt (snd p)) a0) l v'.
Proof. induction l; crush; apply IHl; lia. Qed.

Lemma max_fold_lt4 :
  forall (l: list (positive * Verilog.stmnt)) (a: positive * Verilog.stmnt),
    fold_left (fun a0 p => Pos.max (Verilog.max_reg_stmnt (snd p)) a0) l 1
    <= fold_left (fun a0 p => Pos.max (Verilog.max_reg_stmnt (snd p)) a0) l
                 (Pos.max (Verilog.max_reg_stmnt (snd a)) 1).
Proof. intros; apply max_fold_lt3; lia. Qed.

Lemma max_reg_stmnt_lt_stmnt_tree':
  forall l (i: positive) v,
    In (i, v) l ->
    list_norepet (map fst l) ->
    Verilog.max_reg_stmnt v <= fold_left (fun a p => Pos.max (Verilog.max_reg_stmnt (snd p)) a) l 1.
Proof.
  induction l; crush. inv H; inv H0; simplify. apply max_fold_lt2. lia.
  transitivity (fold_left (fun (a : positive) (p : positive * Verilog.stmnt) =>
                             Pos.max (Verilog.max_reg_stmnt (snd p)) a) l 1).
  eapply IHl; eauto. apply max_fold_lt4.
Qed.

Lemma max_reg_stmnt_le_stmnt_tree :
  forall d i v,
    d ! i = Some v ->
    Verilog.max_reg_stmnt v <= max_stmnt_tree d.
Proof.
  intros. unfold max_stmnt_tree. rewrite PTree.fold_spec.
  apply PTree.elements_correct in H.
  eapply max_reg_stmnt_lt_stmnt_tree'; eauto.
  apply PTree.elements_keys_norepet.
Qed.

Lemma max_reg_stmnt_lt_stmnt_tree :
  forall d i v,
    d ! i = Some v ->
    Verilog.max_reg_stmnt v < max_stmnt_tree d + 1.
Proof. intros. apply max_reg_stmnt_le_stmnt_tree in H; lia. Qed.

Lemma max_stmnt_lt_module :
  forall m d i,
    (mod_controllogic m) ! i = Some d \/ (mod_datapath m) ! i = Some d ->
    Verilog.max_reg_stmnt d < max_reg_module m + 1.
Proof.
  inversion 1 as [ Hv | Hv ]; unfold max_reg_module;
  apply max_reg_stmnt_le_stmnt_tree in Hv; lia.
Qed.

Lemma max_list_correct l st : st > max_list l -> Forall (Pos.gt st) l.
Proof. induction l; crush; constructor; [|apply IHl]; lia. Qed.

Definition max_list_dec (l: list reg) (st: reg) : {Forall (Pos.gt st) l} + {True}.
  refine (
      match bool_dec (max_list l <? st) true with
      | left _ => left _
      | _ => _
      end
    ); auto.
  apply max_list_correct. apply Pos.ltb_lt in e. lia.
Qed.

Definition decide_order a b c d e f g : {module_ordering a b c d e f g} + {True}.
  refine (match bool_dec ((a <? b) && (b <? c) && (c <? d)
                          && (d <? e) && (e <? f) && (f <? g))%positive true with
          | left t => left _
          | _ => _
          end); auto.
  simplify; repeat match goal with
                   | H: context[(_ <? _)%positive] |- _ => apply Pos.ltb_lt in H
                   end; unfold module_ordering; auto.
Defined.

Definition decide_ram_ordering a b c d e f : {ram_ordering a b c d e f} + {True}.
  refine (match bool_dec ((a <? b) && (b <? c) && (c <? d)
                          && (d <? e) && (e <? f))%positive true with
          | left t => left _
          | _ => _
          end); auto.
  simplify; repeat match goal with
                   | H: context[(_ <? _)%positive] |- _ => apply Pos.ltb_lt in H
                   end; unfold ram_ordering; auto.
Defined.

Definition decide_ram_wf (clk : reg) (mr : option HTL.ram) :
  {forall r' : ram, mr = Some r' -> (clk < ram_addr r')%positive} + {True}.
  refine (
      match mr with
      | Some r =>
        match (plt clk (ram_addr r)) with
        | left LE => left _
        | _ => right I
        end
      | None => left _
      end).
  all: crush.
Defined.
