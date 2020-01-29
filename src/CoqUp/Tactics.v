Module Tactics.

  Ltac unfold_rec c := unfold c; fold c.

  Ltac solve_by_inverts n :=
    match goal with | H : ?T |- _ =>
      match type of T with Prop =>
        inversion H;
        match n with S (S (?n')) => subst; try constructor; solve_by_inverts (S n') end
      end
    end.

  Ltac solve_by_invert := solve_by_inverts 1.
  
End Tactics.
Export Tactics.
