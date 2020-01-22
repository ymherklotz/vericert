Module OptionHelpers.

Definition opt_default {T : Type} (x : T) (u : option T) : T :=
  match u with
  | Some y => y
  | None => x
  end.

End OptionHelpers.
Export OptionHelpers.
