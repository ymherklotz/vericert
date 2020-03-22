From coqup.common Require Import Coquplib.

From compcert Require Op Maps.
From compcert Require AST Memory Registers.

Definition node := positive.

Definition reg := Registers.reg.

Inductive instruction : Type :=
| Vnop : node -> instruction
| Vnonblock : Op.operation -> list reg -> reg -> node -> instruction
| Vload : AST.memory_chunk -> Op.addressing -> list reg -> reg -> node -> instruction
| Vstore : AST.memory_chunk -> Op.addressing -> list reg -> reg -> node -> instruction
| Vinst : AST.signature -> reg + AST.ident -> list reg -> reg -> node -> instruction
| Vtailinst : AST.signature -> reg + AST.ident -> list reg -> instruction
| Vcond : Op.condition -> list reg -> node -> node -> instruction
| Vjumptable : reg -> list node -> instruction
| Vfinish : option reg -> instruction.

Definition code : Type := Maps.PTree.t instruction.

(** Function declaration for VTL also contain a construction which describes the
    functions that are called in the current function. This information is used
    to print out *)
Record function : Type :=
  mkfunction {
      fn_sig : AST.signature;
      fn_params : list reg;
      fn_stacksize : Z;
      fn_code : code;
      fn_entrypoint : node;
      fn_calledfuns : list AST.ident
    }.

Definition fundef := AST.fundef function.

Definition design := AST.program fundef unit.

Definition funsig (fd : fundef) :=
  match fd with
  | AST.Internal f => fn_sig f
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
      f.(fn_entrypoint)
      f.(fn_calledfuns).

End TRANSF.

