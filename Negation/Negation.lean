import MathLib
/-
# Copyright, author credits and lean file annotations at: 
https://leannotes.wiki/Proofs/Propositional+Logic/Negation

# Overview:
Double negations can be removed or introduced in pairs.
Another way to express this is to say that:
`Negation equivalence is cyclic with a period of 2.` 

Examples:
  (1) and (2) prove `¬¬P ↔ P`
  (3) and (4) prove `¬¬¬P ↔ ¬P`

`¬P` is _defined_ to mean `P → False`. 
In this sense `¬P`is `syntactic sugar` for the `unsugared` form `P → False`. 
The unsugared implicative form is often preferred because
_implications are foundational_ in the intuitionistic logic that
Lean evaluates by default.
-/
set_option linter.style.emptyLine false -- a preferred LeanNotes format 
variable (P : Prop)
----------------------------------------------------------------------------
-- Examples (1) and (2) prove that ¬¬P ↔ P
-- (1): Negation equivalence is cyclic with a period of 2.
example : ¬¬P → P := by 
  -- Assume the goal's premise.
  intro (h_not_notP : ¬¬P)
  
  -- `FSOC`, assume the goal's negation, `¬P`. 
  by_contra h_notP : ¬P

  -- Apply `MP:` A proposition and its negation cannot both be true.                        
  have hFalse := h_not_notP h_notP

  -- The goal is witnessed, `QED`
  exact show False from hFalse

-- (2): Negation equivalence is cyclic with a period of 2.
example : P → ¬¬P := by

  intro (hP : P)

  -- Unsugar the negated goal.
  change ¬P → False

  -- Assume the goal's premise.
  intro (h_notP : ¬P)

  -- Apply `MP:` A proposition and its negation cannot both be true. 
  have hFalse := h_notP hP

  -- The goal is witnessed, `QED`
  exact show False from hFalse
----------------------------------------------------------------------------
-- Examples (3) and (4) prove that ¬¬¬P ↔ ¬P
-- (3): Negation equivalence is cyclic with a period of 2.
example : ¬¬¬P → ¬P := by
  -- The next four tactics unsugar the goal's premise, `¬¬¬P`.
  -- Unsuger the first (leftmost) negation, 
  intro (hPremise : ¬¬P → False) 
  
  -- Unsuger the second (middle) negation, 
  change (¬P → False) → False at hPremise           

  -- Unsuger the third (rightmost) negation,                 
  change ((P → False) → False) → False at hPremise 

  -- Unsuger the goal's conclusion, `¬P`.
  change P → False                

  -- Assume the goal's premise.
  intro (hP : P)

  -- The goal is the conclusion of an assumed hypotheses,
  -- so it suffices to set the goal to the premise.
  apply hPremise
  
  -- Assume the goal's premise.
  intro (h_PimpFalse : P → False)

  -- Apply `MP:` A proposition and its negation cannot both be true. 
  have hFalse := h_PimpFalse hP 

  -- The goal is witnessed, `QED`
  exact show False from hFalse    

-- (4): Negation equivalence is cyclic with a period of 2.
example : ¬P → ¬¬¬P := by
  -- Assume the goal's premise.
  intro (h_notP : ¬P)

  -- `FSOC`, assume the goal's unsugared negation, `¬P → False`, 
  by_contra h_notPimpFalse : ¬P → False
  
  -- Apply `MP:` A proposition and its negation cannot both be true. 
  have hFalse := h_notPimpFalse h_notP 
  
  -- The goal is witnessed, `QED`
  exact show False from hFalse   
