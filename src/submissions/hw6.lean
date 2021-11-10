import data.set

/-
Exercise: Prove that for any set, L, L ∩ L = L.
-/

example : ∀ (α : Type) (L : set α), L ∩ L = L :=
begin
  assume set_type,
  assume h,
  apply set.ext, -- one argument
  /-@[ext]
theorem ext {a b : set α} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b :=
funext (assume x, propext (h x))-/
  assume n,
  apply iff.intro,
  --forward
    assume p1,
    exact p1.left,
  --backward
    assume p2,
    apply and.intro p2 p2,
end


/-
Exercise: Give a formal statement and proof, then an 
English language proof, that the union operator on 
sets is commutative.
-/

theorem union_commutative : ∀ (α : Type) (L M : set α), L ∪ M = M ∪ L :=
begin
  assume set_α, 
  assume L M,
  apply set.ext, -- one argument
  assume n,
  apply iff.intro, -- two arguments
  --forward
    assume h,
    cases h,
      apply or.intro_right _ h, -- two arguments
      apply or.intro_left _ h, -- two arguments
  --backward
    assume h,
    cases h,
      apply or.intro_right _ h, -- two arguments
      apply or.intro_left _ h, -- two arguments
end


/- 
English Proof:
We assume L is of type set α. Then, we apply the set extensionality
axiom to indicate that x is an element of both set a and set b given they are both of type set α. 
Using the if and only if intro, we divide the bidirectional statement into forward and backward. 
In the first part, we assume the first part of the
implication statement.
Then, we can split this up into two cases. 
Since we know that unions imply one thing or the other as true, we can apply the "introduction rules"
for or to solve these cases. Furthermore, for the backwards case/second part, we can assume the union of the two sets
and splitting this into two cases, we can utilise the left and right or introduction rules to prove that the union
operator on sets is commutative. QED.
-/


/-
Exercise: Prove that ⊆ is reflexive and transitive.
Give a formal statement, a formal proof, and an English
language (informal) proof of this fact.
-/

lemma subset_reflexive : ∀ (α : Type) (L : set α), L ⊆ L :=
begin
  assume α,
  assume L,
  assume a,
  assume h,
  exact h,
end

/-
English/Informal Proof:
We assume that α is of some type and that L is a specific example of type set α.
We assume that a is some version of type α and that a is an element of the L, which is of type set α.
If we assume that that is true, then we can apply the idea that any set of objects of a set L will make up a subset for itself.
This illustrates the reflexive property of a set. QED. 
-/

/-
Exercise: Prove that ∪ and ∩ are associative.
Give a formal statement, a formal proof, and an 
English language (informal) proof of this fact.
-/

lemma union_associative : ∀ (α : Type) (L M N : set α), (L ∪ M) ∪ N = L ∪ (M ∪ N) :=
begin
  assume α,
  assume L M N,
  apply set.ext _,
  assume x,
  apply iff.intro _ _,
  --forward
    assume h,
    apply or.elim h,
    --left
      assume lm,
      apply or.elim lm,
      --left
        assume l,
        exact or.intro_left _ l,
      --right
        assume m,
        exact or.intro_right _ (or.intro_left _ m),
    --right
      assume n,
      exact or.intro_right _ (or.intro_right _ n),
  --backward
    assume h,
    apply or.elim h,
    --left
      assume l,
      exact or.intro_left _ (or.intro_left _ l),
    --right
      assume mn,
      apply or.elim mn,
      --left
        assume m,
        exact or.intro_left _ (or.intro_right _ m),
      --right
        assume n,
        exact or.intro_right _ n,
end

/-
English/Informal Proof (1):
To begin with, we can assume we have a type α, and that sets L, M, and N contain values of this type
α. Then, we apply the set extentionality axiom to turn the set notation into a for all, biimplication statement,
for which we use iff.intro to divide into its forward and backward components.
For the forward case, we assume 
"x ∈ L ∪ M ∪ N", is split into 
x ∈ L, x ∈ M, and x ∈ N. 

To prove "x ∈ L ∪ (M ∪ N)", we use and's introduction rule to split up the proposition into x ∈ L
and x ∈ M ∩ N. The first proposition is proved with the x ∈ L proof and the second proposition is proved by creating a proof of "x ∈ L ∧ x ∈ N" via and's introduction rule and applying it to
the proposition. As for the backwards case, it is proved by assuming "x ∈ L ∩ (M ∩ N)", doing case analysis (twice), 
and applying the and introduction rule to split the final proposition to be proved into "x ∈ L ∩ M" and "x ∈ N". We prove the
second proposition by using one of the many proofs we have for membership of a set via case analysis, and we prove the first proposition
by creating a proof of x ∈ L and x ∈ M via and's introduction rule, and we apply that to the proposition. Finally, we have proved
the associative property of ∩. QED.
-/

/-
Assignment: read (at least skim) the Sections 1 and 
2 of the Wikipedia page on set identities: 
https://en.wikipedia.org/wiki/List_of_set_identities_and_relations 
There, , among *many* other facts, you will find definitions 
of left and right distributivity. To complete the remainder
of this assignment, you need to understand what it means for 
one operator to be left- (or right-) distributive over another. 
-/


/-
Exercise: Formally state, and prove both formally and 
informally, that ∩ is left-distributive over ∩.
-/

theorem intersection_left_distributive_over_intersection : 
  ∀ (α : Type) (L M N : set α), L ∩ (M ∩ N) = (L ∩ M) ∩ (L ∩ N) :=
begin
  assume α,
  assume L M N,
  apply set.ext,
  assume x,
  apply iff.intro _ _,
  --forward
    assume h,
    have l := h.left,
    have mn := h.right,
    have m := mn.left,
    have n := mn.right,
    exact and.intro (and.intro l m) (and.intro l n),
  --backward
    assume h,
    have lm := h.left,
    have l := lm.left,
    have m := lm.right,
    have ln := h.right,
    have n := ln.right,
    exact and.intro l (and.intro m n),
end


/-English Proof:
To begin with, we assume a type α, and that sets L, M, and N are geared towards values of type α. Then, we apply
the set extentionality axiom to the proof in hand, so we can transform it into a more familiar "for all", biimplication
statement. Then, we can assume the existence of value x of type b, and then we can work on proving the left-distributive 
nature of ∩. We apply the intro rule for biimplicational statements, which splits the proof into proving two parts: 
(x ∈ L ∩ (M ∩ N) → x ∈ L ∩ M ∩ (L ∩ N) and (x ∈ L ∩ M ∩ (L ∩ N) → x ∈ L ∩ (M ∩ N)). For the forward statement, we assume 
that x is a member of L ∩ (M ∩ N). We then perform case analysis on this conglomeration of intersections, breaking it up 
on both sides of the intersection to get a proof for x being a member of L, M, and N.
We apply the introduction rule for and. 
As for the backward direction, we first assume (x ∈ (L ∩ M) ∩ (L ∩ N)). Then, we do a case analysis on this proof, and we get various
proofs: x ∈ L, x ∈ M, and x ∈ N. Then, using the and introduction rule, we break the final proposition down further until it the
task at hand is to prove propositions. Since our case analysis yielded us proofs of these propositions,
we simply apply them and prove that ∩ is left-distributive over ∩. QED.-/


/-
Exercise: Formally state and prove both formally 
and informally that ∪ is left-distributive over ∩.
-/


theorem union_left_distributive_over_intersection :
  ∀ (α : Type) (L M N : set α), L ∪ (M ∩ N) = (L ∪ M) ∩ (L ∪ N) :=
begin
  assume α,
  assume L M N,
  apply set.ext _,
  assume x,
  apply iff.intro _ _,
  --forward
    assume h,
    apply or.elim h,
    --left
      assume l,
      exact and.intro (or.intro_left _ l) (or.intro_left _ l),
    --right
      assume mn,
      have m := mn.left,
      have n := mn.right,
      exact and.intro (or.intro_right _ m) (or.intro_right _ n),
  --backward
    assume h,
    have lm := h.left,
    have ln := h.right,
    apply or.elim lm,
    --left
      assume l,
      exact or.intro_left _ l,
    --right
      assume m,
      apply or.elim ln,
      --left
        assume l,
        exact or.intro_left _ l,
      --right
        assume n,
        exact or.intro_right _ (and.intro m n),
end

/-
English/Informal Proof:
To begin with, we assume a type α, and that sets L, M, and N are geared towards values of type α. Then, we apply
the set extentionality axiom to the proof in hand, so we can transform it into a more familiar "for all", biimplication
statement. Then, we can assume the existence of value x of type b, and then we can work on proving the left-distributive 
nature of ∪. We apply the intro rule for biimplicational statements, which splits the proof into proving two parts: 
(x ∈ L ∪ M ∩ N → x ∈ (L ∪ M) ∩ (L ∪ N)) and (x ∈ (L ∪ M) ∩ (L ∪ N) → x ∈ L ∪ M ∩ N). For the forward statement, we assume 
that x is a member of L ∪ (M ∩ N). We then perform case analysis on this conglomeration of operations, breaking it up 
on both sides of the union (L and the paranthetical statement) to get a proof for x being a member of L, M, and N. 
Applying the introduction rule for or, we can break up x ∈ L ∪ M ∩ (L ∪ N) into x ∈ L, x ∈ M, and x ∈ N, because union is
very similar to or in terms of logic. And with the proofs we've derived doing the case analysis, we can apply each and every 
one of these proofs to prove the forward case. As for the backward case, we first assume (x ∈ (L ∪ M) ∩ (L ∪ N)). Then, we do two
case analyses on this proof, and we get various proofs: x ∈ L, x ∈ M, and x ∈ N. Then, using the or and and introduction rules, we break
the final proposition down further until it the task at hand is to prove these tiny little propositions. Since our case 
analysis yielded us proofs of these propositions, we simply apply them and prove that ∪ is left-distributive over ∩. 
QED.
-/