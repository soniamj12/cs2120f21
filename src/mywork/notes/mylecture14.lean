axioms
  (Person : Type)
  (Likes : Person → Person → Prop)


example :
--FORWARDS
--if its not the case that every person p likes themselves (p likes p) (line 1)
--then there is some person p that doesn't like themselves (line 2)
--BACKWARDS
--if there exists somebody who doesn't like themself (line 2)
--then not everyone likes themselves (line 1)

--uninhabited type = empty set = Person is a Type but there are no values of that Type (false)
  ¬ (∀ p : Person , Likes p p) ↔ 
  ∃ p : Person , ¬ Likes p p :=
  begin
    apply iff.intro,
    --forward
    assume h,
    have f := classical.em (∃ (p : Person), ¬Likes p p),
    cases f,
    --case #1: there IS someone who dislikes themself
    assumption,
    --case #2: there IS NOT someone who dislikes themself
    --propose new fact, proof to be constructed in this contradiction1
    have contra : ∀ (p : Person), Likes p p := _,
    --prove current goal using proposed fact
    contradiction,


  --still have to prove supposition
  assume p,

  have g := classical.em (Likes p p),
  cases g,
  exact g, -- you can also use assumption or trivial here
  have a : ∃ (p : Person), ¬ Likes p p := exists.intro p g,
  contradiction,


  --backward
  assume h,
  cases h with p l,
  assume a,
  have d := a p,

  end




  def func : ∀ (n : ℕ), ℕ := 
    begin
      assume h,
      exact h,
    end


  #reduce func 3