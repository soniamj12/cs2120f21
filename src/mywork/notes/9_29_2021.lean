axioms
  (Ball : Type)
  (Green : Ball → Prop)
  (Red : Ball → Prop)
  (b1 b2 : Ball)
  (b1r : Red b1)
  (b1g : Green b1)
  (b2r : Red b2)


example : 
  (∃ (b : Ball), Red b ∧ Green b) → 
  (∃ (b : Ball), Red b) :=
  begin
    assume h,
    cases h with b rg,
    apply exists.intro b,
    exact rg.left,
  end


  -- example :
  --   (∃ (b : Ball), Red b ∨ Green b) → 
  --   (∃ (b : Ball), Green b ∨ Red b) :=
  -- begin
  --   assume h,
  --   cases h with w pf,
  --   apply exists.intro w,
  --   cases pf,
  --   _
  -- end


  -- example :
  --   (∃ (b : Ball), Red b ∨ Green b) → 
  --   (∃ (b : Ball), Red b) :=
  -- begin
  --   assume h,
  --   cases h with w pf,
  --   cases pf,
  --   apply exists.intro w,
  --   assumption,
  --   apply exists.intro w,
  --   --can't go any further
  -- end



axioms
  (Person: Type)
  (Nice: Person → Prop)
  (Likes: Person → Person → Prop)

example :
  (∃ (p1 : Person), ∀ (p2 : Person), Likes p2 p1) →
  (∀ (e : Person), ∃ (s : Person), Likes e s) :=
begin,
   assume h,
   assume p1,
   cases h with p pf,
   apply exists.intro p,
   exact (pf e),
end




