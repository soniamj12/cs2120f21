/-Induction Principle for the Bool Type-/

/-Proof by induction-/

/-
let's say than n is of type ℕ with property P
for all values n that successively increase by value 1
we must assume that n = k is true and use that to prove n = k + 1 is true by induction


The idea is that if you want to show that someone can climb to the nth floor of a fire 
escape, you need only show that you can climb the ladder up to the fire escape (n=1) and 
then show that you know how to climb the stairs from any level of the fire escape (n=k) 
to the next level (n=k+1).

for all n', if property is true for n', then it must be true for n'+1


assume that you have an answer for n' and use that as the basis for proving n'+1
---> establishes the second rule for induction
lema 1 --> property holds true for 0
lema 2 --> induction on natural numbers


P 0 -- obvious
∀ n' P n' → P(n' + 1)
Assume n' , ih : P n'
induction hypothesis says --> P n' (assume that P holds for n')


so we can say sum of i's from i = 0 to n'+1 is equal to sum of i's from i = 0 to n' plus (n' + 1)
so then that equals (n'(n' + 1)/2) + (2(n' + 1)/2) --> do the algebra for this
-/



