import MathLib
/-
# Copyright, author credits and lean file annotations at: 
https://leannotes.wiki/Proofs/Propositional+Logic/Negation
-/
set_option linter.style.emptyLine false -- allow empty lines in proofs
variable (P : Prop)

--------------------------------------------------------------------------------
-- Examples (1) and (2) prove that ¬¬P ↔ P
--------------------------------------------------------------------------------
-- (1) *Negations can be decremented in pairs.*
example : ¬¬P → P := by 
  intro (h_notPimpFalse : ¬P → False)
  by_contra h_notP : ¬P
  have hFalse := h_notPimpFalse h_notP
  exact show False from hFalse

-- (2) *Negations can be incremented in pairs.*
example : P → ¬¬P := by
  intro (hP : P)
  change ¬P → False
  intro (hPimpFalse : P → False)  
  have hFalse := hPimpFalse hP
  exact show False from hFalse

--------------------------------------------------------------------------------
-- Examples (3) and (4) prove that ¬¬¬P ↔ ¬P
--------------------------------------------------------------------------------
-- (3): *An odd number of negations can be decremented in pairs.*
example : ¬¬¬P → ¬P := by
  intro (hPremise : (¬P → False) → False)                           
  change P → False               
  intro (hP : P)
  apply hPremise
  intro (hPimpFalse : P → False)
  have hFalse := hPimpFalse hP
  exact show False from hFalse

-- (4): *An odd number of negations can be incremented in pairs.*
example : ¬P → ¬¬¬P := by
  intro (h_notP : ¬P)
  by_contra (h_not_notP : ¬¬P)
  have hFalse := h_not_notP h_notP
  exact show False from h_not_notP h_notP
