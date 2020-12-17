From compcert Require Import
     Maps
     AST
     RTL.

Parameter pipeline : function -> function.

Definition transf_fundef := transf_fundef pipeline.

Definition transf_program : program -> program :=
  transform_program transf_fundef.
