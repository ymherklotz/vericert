From coqup.common Require Import Coquplib.

From compcert Require Op Maps.
From compcert Require AST Memory Registers.

Definition node := positive.

Definition reg := Registers.reg.

Definition ident := AST.ident.

Inductive instruction : Type :=
| Vnop : node -> instruction
| Vnonblock : Op.operation -> list reg -> reg -> node -> instruction
| Vload : AST.memory_chunk -> Op.addressing -> list reg -> reg -> node -> instruction
| Vstore : AST.memory_chunk -> Op.addressing -> list reg -> reg -> node -> instruction
| Vinst : AST.signature -> ident -> list reg -> reg -> node -> instruction
| Vtailinst : AST.signature -> ident -> list reg -> instruction
| Vcond : Op.condition -> list reg -> node -> node -> instruction
| Vjumptable : reg -> list node -> instruction
| Vfinish : option reg -> instruction.

Record inst : Type :=
  mkinst {
inst_start : reg;
inst_finish : reg;
inst_result : reg;
inst_args : list reg
}.

Definition code : Type := Maps.PTree.t instruction.

Definition instantiations : Type := Maps.PTree.t inst.

(** Function declaration for VTL also contain a construction which describes the
    functions that are called in the current function. This information is used
    to print out *)
Record module : Type :=
  mkmodule {
      mod_sig : AST.signature;
      mod_params : list reg;
      mod_stacksize : Z;
      mod_code : code;
      mod_insts : inst;
      mod_entrypoint : node
    }.

Definition moddef := AST.fundef module.

Definition design := AST.program moddef unit.

Definition modsig (md : moddef) :=
  match md with
  | AST.Internal m => mod_sig m
  | AST.External ef => AST.ef_sig ef
  end.

(** Describes the transformation of VTL instruction by instruction. This applies
    the transformation to each instruction in the function and returns the new
    function with the modified instructions. *)
Section TRANSF.

  Variable transf : node -> instruction -> instruction.

  Definition transf_function (f : function) : function :=
    mkfunction
      f.(fn_sig)
      f.(fn_params)
      f.(fn_stacksize)
      (Maps.PTree.map transf f.(fn_code))
      f.(fn_entrypoint).

End TRANSF.
