import data.set

/-
CS2120 F21 HW5

The goals of this assignment are to give you
practice with proofs of propositions that use
existential quantificaton, and to develop your
understanding of formal and informal proofs in
set theory.
-/

/-
PART I: EXISTENTIAL QUANTIFICATION.
-/

/-
To start, suppose that α and β are arbitrary
types, and p and q are predicates on values
of these types: α and β, respectively.
-/

axioms 
  (α β : Type)    -- data types
  (p : α → Prop)  -- predicates
  (q : β → Prop)

/-
In this context complete the following tasks:

(1) Write a fluent English-language statement
of the proposition to be proved. 

(2) Provide a formal proof of the proposition.

(3) Write an informal proof of the proposition.
-/

-- here's the proposition
example : 
  (∃ (f : α → β), ∀ (a : α), p a → q (f a)) →
  (∃ (a : α), p a) → 
  (∃ (b : β), q b) := 

/-
What does this propositon say? Explain it in
plain English. Here's a start: "If there's a 
function that maps/takes every α value that ... 
-- your completed English rendition here:

If there's a function that maps every α value to a β value,
then all objects a of type α and property p translate to objects (f a) consisting of property q,
such that there exists an object a of type α with property p and an object b of type β
with property q.

-/


-- Give your formal proof here
begin
  assume h,
  assume n,
  cases h with x pf,
  cases n with x2 pf2,
  apply exists.intro (x x2),
  exact (pf x2 pf2),
end
  

/-
Informal Proof:
We begin with an implication, so we assume that the first statement is true: ∃ (f : α → β), ∀ (a : α), p a → q (f a).
This means that there exists some function that translates objects of type α to those of type β, and that when this
translation is done, the resulting value (f a) has property q of objects classified as type β. 
There's a second implication as well that we need to assume: ∃ (a : α), p a.
This one is pretty simple -- it's just saying that there exists some object a of type α, and that because it is of this
particular type, it has the property p that characterizes that type of object.
Now we're left to prove ∃ (b : β), q b.
We use case analysis over our assumptions to begin proving this.
This acts as a witness ot the existential proposition that confirms that there exists a value of type β,
meaning that there must be property q for objects of type β.
We have to do case analysis again, this time for objects of type α and property p.
Since these both pass case analysis and confirm that the two exist, we can apply exists.intro and then
invoke the proofs formed by doing the case analysis.
-/