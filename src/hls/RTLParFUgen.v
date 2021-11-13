Require Import Coq.micromega.Lia.

Require Import compcert.common.AST.
Require compcert.common.Errors.
Require compcert.common.Globalenvs.
Require compcert.lib.Integers.
Require Import compcert.lib.Maps.

Require Import vericert.common.Statemonad.
Require Import vericert.common.Vericertlib.
Require Import vericert.hls.AssocMap.
Require Import vericert.hls.HTL.
Require Import vericert.hls.Predicate.
Require Import vericert.hls.RTLParFU.
Require Import vericert.hls.ValueInt.
Require Import vericert.hls.Verilog.
Require Import vericert.hls.RTLBlockInstr.
Require Import vericert.hls.RTLPar.

Definition transl_program (p : RTLParFU.program) : Errors.res HTL.program :=
  transform_partial_program transl_fundef p.
