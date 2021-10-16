--no proposition can be both true and false



theorem no_contradiction : ∀ (P : Prop), ¬(P ∧ ¬P) :=
begin
  assume p,
  assume pp,
  cases pp,
  apply false_of_true_eq_false,
  apply false.elim _,
  exact (pp_right pp_left),
end


theorem no_contradiction : ∀ (P : Prop), ¬(P ∧ ¬P) :=
begin
  assume p,
  assume pp,
  have p := pp.left,
  have np := pp.right,
  have f := np p, --*****
  exact f,
end


axiom excluded_middle : ∀ (P : Prop), (P ∨ ¬P)