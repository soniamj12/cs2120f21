--INFERENCE RULE #1/2: EQUALITY IS REFLEXIVE (eq.refl)


/-
Everything is equal to itself. A bit more formally,
if one is given a type, T, and a value, t, of this
type, then you may have a proof of t = t "for free."
-/

/-For all objects t of type T, t = t. This is known as the reflexive
property of equality and it justifies why the natural number 2 = 2.-/

example : 2 = 2 := @eq.refl ℕ 2

def reflex
  (T : Type)
  (t : T)
  : t = t
  := eq.refl t

#reduce reflex ℕ 2


/-Axiom for Reflexive Property of Equality-/
axiom eq_ref :
  ∀ (T : Type) -- for all objects of type T
  (t : T), -- such that t as an object of type T
t = t -- t must equal itself


--INFERENCE RULE #2/2: SUBSTITUTION OF EQUALS FOR EQUALS (eq.subst)


/-
Given any type, T, of objects, and any *property*, P,
of objects of this type, if you know x has property P
(written as P x) and you know that x = y, then you can
deduce that y has property P.
-/


/-Axiom for Substitution of Equals for Equals-/
axiom eq_sub :
∀ (T : Type) -- for all objects of type T
  (P : T → Prop) -- with property P of type T
  (x y : T) -- if we have variables x and y of type T
  (e : x = y) -- such that they are equal to each other
  (px : P x), -- and x has property P
P y -- then y must have property P






--Theorem: Symmetry of Equality

/-
What it means for equality to be symmetric is that *if*
x = y (for *any* x and y), then it must also be that y = x.
-/



--Theorem: Transitivity of Equality

/-
When we say that a relation r, is transitive, we mean that, 
for all objects, x, y, and z, if x is related to y by r, and 
y is is related to z by r, then x must be related to z by r 
(otherwise r is not transitive).
-/