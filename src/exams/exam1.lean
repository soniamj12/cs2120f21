/- 
   *******************************
   PART 1 of 2: AXIOMS [50 points]
   *******************************
-/

/-
Explain the inference (introduction and
elimination) rules of predicate logic as
directed below. To give you guidance on
how to answer these questions we include
answers for some questions.
-/


-- -------------------------------------

/- #1: → implies [5 points]

INTRODUCTION

Explain the introduction rule for →. 

[We give you the answer here.]

In English: Given propositions, P and Q, 
a derivation (computation) a proof of Q 
from any proof of P, is a proof of P → Q.

In constructive logic, a derivation is a
given as a function definition. A proof
of P → Q literally is a function, that,
when given any proof of P as an argument
returns a proof of Q. If you define such
a function, you have proved P → Q.

ELIMINATION

Complete the definition of the elimination
rule for →.

(P Q : Prop) (p2q : P → Q) (p : P)
--------------------------------- → elim
              q : Q

-/

-- Give a formal proof of the following
example : ∀ (P Q : Prop) (p2q : P → Q) (p : P), Q :=
begin
  assume p q,
  assume pq,
  exact pq,
end

-- Extra credit [2 points]. Who invented this principle?

-- Answer: Theophrastus

-- -------------------------------------


/- #2: true [5 points]

INTRODUCTION

Give the introduction rule for true using
inference rule notation.

[Here's our answer.]

---------- intro
(pf: true)

Give a brief English language explanation of
the introduction rule for true.

-- Answer: because truth should always be true, its introduction rule has no premises.

ELIMINATION

Give an English language description of the
eliimination rule for true.

[Our answer]

A proof of true carries no information so
there's no use for an elimination rule.
-/

-- Give a formal proof of the following:

example : true := 
begin
  exact true.intro,
end

-- -------------------------------------

/- #3: ∧ - and [10 points]

INTRODUCTION

Using inference rule notation, give the 
introduction rule for ∧.

[Our answer]

(P Q : Prop) (p : P) (q : Q)
---------------------------- intro
        (pq : P ∧ Q)


Given an English language description of
this inference rule. What does it really
say, in plain simple English. 

-- Answer: For propositions P and Q such that p is assumed to exist as type P and 
  q is of type Q, then the statement pq must be true such that both P and Q are true.

ELIMINATION

Give the elimination rules for ∧ in both
inference rule and English language forms.
-/

--Inference Rules:
/-
(P Q : Prop) (pq : P ∧ Q)
------------------------- ∧ elim (left)
        p : P

(P Q : Prop) (pq : P ∧ Q)
------------------------- ∧ elim (right)
          q : Q
-/

--English Language: 
/-
Answer: 
Left - For propositions P and Q such that p is of type pq is of type P ∧ Q, then p of type P must
be true in order to satisfy that pq is true.
Right - For propositions P and Q such that p is of type pq is of type P ∧ Q, then q of type Q must
be true in order to satisfy that pq is true.
-/

/-
Formally state and prove the theorem that, 
for any propositions P and Q,  Q ∧ P → P. 
-/
example : ∀ (P Q : Prop), Q ∧ P → P := 
begin
  assume P Q,
  assume h,
  apply and.elim h,
  assume q,
  assume p,
  exact p,
end

-- -------------------------------------

/- #4: ∀ - for all [10 points]

INTRODUCTION

Explain in English the introduction rule for ∀. If 
T is any type (such as nat) and Q is any proposition 
(often in the form of a predicate on values of the
given type), how do you prove ∀ (t : T), Q? What is
the introduction rule for ∀?

-- If there is a specific object of property P, 
then we know that there exists is some object that has property P

ELIMINATION

Here's an inference rule representation of the elim
rule for ∀. First, complete the inference rule by
filling in the bottom half, then Explain in English
what it says.

(T : Type) (P : T → Prop) (a : ∀ (x : T), P x) (t : T)
------------------------------------------------------ ∀ elim
                        pf: P t

-- Every x of type T has property P, so we apply a to t, which
then yields a proof that t, in particular, satisfies
the predicate P (has property P).

Given a proof, (pf : ∀ (t : T), Q), and a value, (t : T),
briefly explain in English how you *use* pf to derive a
proof of Q.

-- You can *apply* pf to an object t of property T to derive a proof of some proposition Q.
-/

/-
Consider the following assumptions, and then in the
context of these assumptions, given answers to the
challenge problems.
-/

axioms
  (Person : Type)
  (KnowsLogic BetterComputerScientist : Person → Prop)
  (LogicMakesYouBetterAtCS: 
    ∀ (p : Person), KnowsLogic p → BetterComputerScientist p)
  -- formalizee the following assumptions here
  -- (1) Lynn is a person
  -- (2) Lynn knows logic
    (Lynn : Person) --(1)
    (LynnKnowsLogic : KnowsLogic Lynn) --(2)

/-
Now, formally state and prove the proposition that
Lynn is a better computer scientist
-/
example : BetterComputerScientist Lynn := 
begin
  apply LogicMakesYouBetterAtCS Lynn,
  exact LynnKnowsLogic,
end



-- -------------------------------------

/- #5: ¬ - not [10 points] 

The ¬ connective in Lean is short for *not*. Give
the short formal definition of ¬ in Lean. Note that
surround the place where you give your answer with
a namespace. This is just to avoid conflicting with
Lean's definition of not.
-/

namespace hidden
def not (P : Prop) := P → false -- fill in the placeholder
end hidden

/-
Explain precisely in English the "proof strategy"
of "proof by negation." Explain how one uses this
strategy to prove a proposition, ¬P. 
-/

/- 
PROOF BY NEGATION
We've shown above that ¬P is synonymous to P → false.
But there's no proof of false, so we cannot identify P as false.
What we can do is show that there is a contradiction when assuming that P is true, which would mean
that the only other identification of P would have to be false.

"assume P, show that that leads to some kind
of contradiction, and conclude P → false. This
is the precondition for deducting ¬P."
-/

/-
Explain precisely in English the "proof strategy"
of "proof by contradiction." Explain how one uses
this strategy to prove a proposition, P (notice 
the lack of a ¬ in front of the P). 

Fill in the blanks the following partial answer:

To prove P, assume ¬P and show that the assumption yields a contradiction.
From this derivation you can conclude ¬¬P.
Then you apply the rule of negation elimination
to that result to arrive a a proof of P. We have
seen that the inference rule you apply in the 
last step is not constructively valid but that it
is clasically valid, and that accepting the axiom
of the law of excluded middle suffices to establish negation
elimination (better called double negation elimination)
as a theorem.
-/



-- -------------------------------------

/- 
#6: ↔ - if and only if, equivalent to [10 points]
-/

/-
ELIMINATION 

As with ∧, ↔ has two elimination rules. You can 
see their statements here.
-/
#check @iff.elim_left
#check @iff.elim_right

/-
Formally state and prove the theorem that 
biimplication, ↔, is *commutative*. Note: 
put parentheses around each ↔ proposition,
as → has higher precedence than ↔. Recall
that iff has both elim_left and elim_right
rules, just like ∧.
-/

example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P:=
begin
  assume P Q,
  apply iff.intro _ _,
  --forward
    assume pq,
    cases pq,
    apply and.intro pq_right pq_left,
  --backward
    assume qp,
    cases qp,
    apply and.intro qp_right qp_left,
end


/- 
   ************************************************
   PART 2 of 3: PROPOSITIONS AND PROOFS [50 points]
   ************************************************
-/

/- #7 [20 points]

First, give a fluent English rendition of
the following proposition. Note that the
identifier we use, elantp, is short for
"everyone likes a nice, talented person."
Then give a formal proof. Hint: try the
"intros" tactic by itself where you'd
previously have used assume followed by
a list of identifiers. Think about what
each expression means. 
-/

/-
For all individuals of type Person, every person likes someone who is nice and talented. 
Since John Lennon is a person everyone likes, he must be nice and talented.
-/

def ELJL : Prop := 
  ∀ (Person : Type) 
    (Nice : Person → Prop)
    (Talented : Person → Prop)
    (Likes : Person → Person → Prop)
    (elantp : ∀ (p : Person), 
      Nice p → Talented p → 
      ∀ (q : Person), Likes q p)
    (JohnLennon : Person)
    (JLNT : Nice JohnLennon ∧ Talented JohnLennon),
    (∀ (p : Person), Likes p JohnLennon) 
    

example : ELJL :=
begin
  intros Person Nice Talented Likes elantp JohnLennon JLNT p,
  apply elantp JohnLennon _ _,
  exact and.elim_left JLNT,
  exact and.elim_right JLNT,
end



/- #8 [10 points]

If every car is either heavy or light, and red or 
blue, and we want a prove by cases that every car 
is red, then: 

-- how many cases will need to be considered? 4
-- list the cases (informally)
    -- 1 - heavy red
    -- 2 - heavy blue
    -- 3 - light red
    -- 4 - light blue

-/

/-
  *********
  RELATIONS
  *********
-/


/- #9 [20 points]
Equality can be understood as a binary relation
on objects of a given type. There is a binary 
equality relation on natural numbers, rational 
numbers, on strings, on Booleans, and so forth.

We also saw that from the two axioms (inference
rules) for equality, we could prove that it is
not only reflexive, but also both symmetric and
transitive.

Complete the following definitions to express
the propositions that equality is respectively
symmetric and transitive. (Don't worry about
proving these propositions. We just want you
to write them formally, to show that you what
the terms means.)
-/

def eq_is_symmetric : Prop :=
  ∀ (T : Type) (x y : T), x = y → y = x

def eq_is_transitive : Prop :=
  ∀ (T : Type) (x y z : T), x = y → y = z → x = z


/-
  ************
  EXTRA CREDIT
  ************
-/

/- 
EXTRA CREDIT: State and prove the proposition
that (double) negation elimination is equivalent
to excluded middle. You get 1 point for writing
the correct proposition, 2 points for proving it
in one direction and five points for proving it
both directions. 
-/

def negationelim_excludedmid : Prop := 
  ∀ (P : Prop), (P → ¬¬P) ↔ (P ∨ ¬P)

example : negationelim_excludedmid:=
begin
  unfold negationelim_excludedmid,
  assume P,
  apply iff.intro,
  assume h,
  apply classical.em P,
  assume x,
  assume P,
  assume n,
  contradiction,
end


/- 
EXTRA CREDIT: Formally express and prove the
proposition that if there is someone everyone
loves, and loves is a symmetric relation, then 
thre is someone who loves everyone. [5 points]
-/

axiom Loves : Person → Person → Prop
axiom Loves_symm : ∀ (p everyone : Person), Loves everyone p → Loves p everyone

-- -----

example :   
  (∃ (p : Person), ∀ (everyone: Person), Loves everyone p) →  
  (∃ (p : Person), ∀ (everyone: Person), Loves p everyone)  := 
begin
  assume h,
  cases h,
  apply exists.intro h_w _,
  assume n,
  have loves_all : Loves h_w n := _,
  exact loves_all,
  have symmetry := Loves_symm h_w n,
  have case_everyone := h_h n,
  have result := symmetry case_everyone,
  exact result,
end
