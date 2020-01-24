Module Option.

Definition default {T : Type} (x : T) (u : option T) : T :=
  match u with
  | Some y => y
  | None => x
  end.

Definition map {S : Type} {T : Type} (f : S -> T) (u : option S) : option T :=
  match u with
  | Some y => Some (f y)
  | None => None
  end.

End Option.
