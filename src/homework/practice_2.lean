/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.
-/

example : true := true.intro



-- example : false := _    -- trick question? why?
/-
You can't fill this in because there is no proof of false. 
The definition of false is that there are no proofs.
-/




/-
Elimination Rule for ∨: X ∨ Y → Z
Prove X → Z, Y → Z
-/

/-P or P implies P -- assume P or P is true and use that to show either
P is true or P is true-/
example : ∀ (P : Prop), P ∨ P ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  -- forward 
    assume porp,
    apply or.elim porp,
    --left disjunct is true
      assume p,
      exact p,
    --right disjunct is true
      assume p,
      exact p,
  -- backward
    assume pp,
    apply or.intro_left P pp,
end





example : ∀ (P : Prop), P ∧ P ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  -- forward
    assume p,
    apply and.elim p,
    assume pp,
    assume ppp,
    exact ppp,

  -- backward
    assume p,
    apply and.intro _ _,
    exact p,
    exact p,
end




example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
begin
  assume P,
  assume Q,
  apply iff.intro _ _,
  --front
    assume p,
    apply or.elim,
    exact p, 
    apply or.intro_right,

    assume q,
    apply or.intro_left,
    exact q, 
  --back
    assume q2,
    apply or.elim,
    exact q2,
    apply or.intro_right,

    assume p2,
    apply or.intro_left,
    apply p2,
end





example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  --front
    assume p,
    apply and.elim,
    exact p,
    assume pp,
    assume qq,
    apply and.intro,
    exact qq,
    exact pp,

  --back
    assume q,
    apply and.elim,
    exact q,
    assume qq,
    assume pp,
    apply and.intro,
    exact pp,
    exact qq,
end





example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
  assume P Q R,
  apply iff.intro _ _,

  assume prop,
  apply and.elim prop,
  assume p,
  assume prop2,
  apply or.elim prop2,
  assume q,
  apply or.intro_left,
  apply and.intro _ _,
  exact p,
  exact q,
  assume r,
  apply or.intro_right,
  apply and.intro _ _,
  exact p,
  exact r,

  assume prop,
  apply or.elim prop,
  assume prop2,
  apply and.elim prop2,
  assume p,
  assume q,
  apply and.intro _ _,
  exact p,
  apply or.intro_left,
  exact q,

  assume prop3,
  apply and.elim prop3,
  assume p,
  assume r,
  apply and.intro _ _,
  exact p,
  apply or.intro_right,
  exact r,
  -- assume P Q R,
  -- apply iff.intro _ _,

  -- assume prop,
  -- apply and.elim prop,
  -- assume p,
  -- assume qr,
  -- apply or.elim,
  -- apply or.intro_left,
  -- exact prop,


  -- assume P Q R,
  -- apply iff.intro _ _,
  -- --front
  --   assume p,
  --   apply and.elim p,
  --   assume pp,
  --   assume qr,
  --   apply or.intro_left,
  --   apply and.intro,
  --   exact pp,
  --   apply or.elim,
  --   exact qr, 
  --   assume q,
  --   exact q,
  --   assume r,
    
  -- --back
end

example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
    assume P Q R,
  apply iff.intro _ _,

  assume prop,
  apply or.elim prop,
  assume p,
  apply and.intro,
  apply or.intro_left,
  exact p,
  apply or.intro_left,
  exact p,
  assume prop2,
  apply and.elim prop2,
  assume q,
  assume r,
  apply and.intro,
  apply or.intro_right,
  exact q,
  apply or.intro_right,
  exact r,

  assume prop,
  have pq :(P ∨ Q) := and.elim_left prop,
  have pr :(P ∨ R) := and.elim_right prop,
  apply or.elim pq,
  assume p,
  apply or.intro_left,
  exact p,
  assume q,
  apply or.elim pr,
  assume p,
  apply or.intro_left,
  exact p,
  assume r,
  apply or.intro_right,
  apply and.intro,
  exact q,
  exact r,
end

example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  assume prop,
  apply and.elim prop,
  assume p,
  assume prop2,
  exact p,
  assume p,
  apply and.intro _ _,
  exact p,
  apply or.intro_left,
  exact p,
end

example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  assume prop,
  apply or.elim prop,
  assume p,
  exact p,
  assume prop2,
  apply and.elim prop2,
  assume p,
  assume q,
  exact p,
  assume p,
  apply or.intro_left,
  exact p,
end

example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
  assume P,
  apply iff.intro,
  assume prop,
  exact true.intro,
  assume t,
  apply or.intro_right,
  exact t,
end

example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
  assume P,
  apply iff.intro,
  assume prop,
  apply or.elim prop,
  assume p,
  exact p,
  apply false.elim,
  assume p,
  apply or.intro_left,
  exact p, 
end

example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
  assume P,
  apply iff.intro,
  assume prop,
  apply and.elim prop,
  assume p,
  assume t,
  exact p,
  
  assume p,
  apply and.intro,
  exact p,
  exact true.intro,
end

example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
  assume P,
  apply iff.intro,
  assume prop,
  apply and.elim prop,
  assume p,
  assume f,
  exact f,
  apply false.elim,
end


