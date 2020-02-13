Module Option.

Definition default {T : Type} (x : T) (u : option T) : T :=
  match u with
  | Some y => y
  | _ => x
  end.

Definition map {S : Type} {T : Type} (f : S -> T) (u : option S) : option T :=
  match u with
  | Some y => Some (f y)
  | _ => None
  end.

Definition liftA2 {T : Type} (f : T -> T -> T) (a : option T) (b : option T) : option T :=
  match a with
  | Some x => map (f x) b
  | _ => None
  end.

End Option.
