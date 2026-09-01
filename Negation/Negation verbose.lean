import MathLib
/-
# Copyright, author credits and lean file annotations at: 
https://leannotes.wiki/Proofs/Propositional+Logic/Negation

# Overview:
*Double negations can be cancelled or introduced in pairs:* 

   `¬¬P ↔ P`
  `¬¬¬P ↔ ¬P`

Negation of a proposition, `¬P` is *definitionally equal* to the implication
that the proposition implies falsity, `P → False`:

  `¬P ☰ P → False` 

*Proof strategies:*  
* It is a useful proof technique to  `desugar` or `disassemble` a negation into 
its implicative form.

* When there are multiple negations a good strategy is to leave the 
innermost negation in sugared form and to desugar the rest:

  _Double negation desugared rule_:
    `¬¬P` 
  `☰ ¬(¬P)` 
  `☰   ¬P → False`

  _Triple negation desugared rule_:
    `¬¬¬P` 
  `☰ ¬(¬¬P)` 
  `☰   ¬¬P → False`
  `☰   ¬(¬P) → False`
  `☰    (¬P → False) → False`
-/

set_option linter.style.emptyLine false -- allow empty lines in proofs
variable (P : Prop)

--------------------------------------------------------------------------------
-- Examples (1) and (2) prove that ¬¬P ↔ P
--------------------------------------------------------------------------------
-- (1) *Negations can be decremented in pairs.*
example : ¬¬P → P := by 
  -- We assume the theorem's premise, `¬¬P`, and
  -- shift the goal to the conclusion, `P`.

  -- Also, we apply the _Double negation desugared rule_ to the premise.
  intro (h_notPimpFalse : ¬P → False)

  -- A proof by contradiction is available via 
  --    `MP: ¬P → False, ¬P ⊢ False`
  -- as follows:
  
  -- The `first MP premise` is provided by the 
  -- theorem's premise: `h_notPimpFalse : ¬P → False`
   
  -- The `second MP premise` is equivalent to the negated goal, `¬P`.
  -- The *by_contra* tactic assumes this negated goal
  -- and it sets the new goal to the `MP conclusion`, `⊢ False`.
  by_contra h_notP : ¬P

  -- We apply `MP` to match the goal, `⊢ False`, `QED`.
  have hFalse := h_notPimpFalse h_notP
  exact show False from hFalse

-- (2) *Negations can be incremented in pairs.*
example : P → ¬¬P := by
  -- We assume the theorem's premise, `P`, and
  -- shift the goal to the conclusion in desugared form, `¬¬P ☰ ¬P → False`.
  intro (hP : P)
  change ¬P → False

  -- We assume the goal's premise, `h_notP : ¬P` and
  -- shift the goal to the conclusion in desugared form, `⊢ P → False`. 
  intro (hPimpFalse : P → False)  

  -- A proof by contradiction is available via 
  --    `MP: P → False, P ⊢ False`
  -- as follows:
  
  -- `MP first premise:` This is equivalent to the negated goal
  --    in desugared form, `¬(¬¬P) ☰ ¬P ☰ P → False`.
  --    The *by_contra* tactic assumes this negated goal.
  
  -- `MP second MP:` This is provided by the theorem's premise: `hP : P`

  -- `MP conclusion:` The *by_contra* tactic sets the goal to `⊢ False`.
  by_contra h_notP : P → False
  
  -- We apply `MP` to match the goal, `⊢ False`, `QED`.
  have hFalse := h_notP hP
  exact show False from hFalse

--------------------------------------------------------------------------------
-- Examples (3) and (4) prove that ¬¬¬P ↔ ¬P
--------------------------------------------------------------------------------
-- (3): *An odd number of negations can be decremented in pairs.*
example : ¬¬¬P → ¬P := by
  -- We assume the theorem's premise in desugared form, `(¬P → False) → False`,
  -- and shift the goal to the conclusion, `¬P`

  intro (hPremise : ¬¬¬P) 
  change (¬¬P → False)        at hPremise                           
  change (¬P → False) → False at hPremise                           

  -- We also desugar the goal: `¬P ☰ P → False`.
  change P → False   

  -- We assume the goal's premise, `hP : P` and
  -- shift the goal to the conclusion, `⊢ False`.             
  intro (hP : P)

  -- Given that the goal is false, we strive to set up a
  -- `contradictory MP application`.

  -- The *apply* tactic can move the proof forward since
  -- the goal, `¬ False`, is the conclusion of an assumed hypothesis, 
  -- `hPremise : (¬P → False) → False`.
  -- The new goal is reduced to the assumed hypthesis premise, `¬P → False`.
  apply hPremise

  -- We assume the goal's premise in desugared form, `¬P ☰ P → False`,
  -- and shift the goal to the conclusion, `⊢ False`.
  intro (hPimpFalse : P → False)

  -- A `contradictory MP application` will match the goal, `⊢ False`, `QED`.
  have hFalse := hPimpFalse hP
  exact show False from hFalse

example : ¬¬¬P → ¬P := by
  -- Assume the goal's premise in unsuger form, in three steps
  intro (hPremise : ¬¬¬P) 
  change (¬¬P → False) at hPremise                           
  change ( ¬P → False) → False at hPremise                           
  change ( (P → False) → False) → False at hPremise 

  -- Unsuger the goal's conclusion, `¬P` and assume its premise, `P`,
  change P → False                
  intro (hP : P)

  -- The goal is the conclusion of an assumed hypotheses,
  -- so it suffices to set the goal to the premise, `((P → False) → False)`
  -- which is also the premise of `hPremise : ((P → False) → False) → False`
  apply hPremise
  
  -- (1) Assume the goal's premise, `h : notP : ¬P`,
  -- which also the negation of `hP : P`
  -- The goal is now `⊢ FALSE`, so we obtain a contradiction.
  -- (2) Tht is, the `False` goal is witnessed by `h_notP hP`, 
  --     since `P` and its negation `¬P` cannot both be true, `QED`
  intro (h_notP : ¬P)
  exact show False from h_notP hP    

-- (4): *An odd number of negations can be incremented by 2.*
example : ¬P → ¬¬¬P := by
  -- Assume the goal's premise.
  intro (h_notP : ¬P)

  -- (1) `FSOC`, assume the goal's negation, `h_not_notP : ¬¬P`, 
  -- which also the negation of `hP : ¬P`.
  -- The goal is now `⊢ FALSE`, so we obtain a contradiction.
  -- (2) That is, the `False` goal is witnessed by `h_notP hP`, 
  --     since `¬P` and its negation `¬(¬P)` cannot both be true, `QED`
  by_contra h_not_notP : ¬¬P
  exact show False from h_not_notP h_notP


theorem double_neg_intro_term : P → ¬¬P := 
  -- This theorem is proved most conveniently by using the
  -- desugared form of negation: `¬P = P → False`.
  -- So, the fully desugared form of the theorem is:
  --
  -- `P → (¬P -> False)` =
  -- `P → ((P → False) → False`,
  -- where the goal is to witness `False`
  --
  -- The proof then becomes, in English: 
  -- if is assumed that `P` is true, and
  --    if it is further assumed that `(P → False)` is true,
  -- then we can apply `MP: (P → False), P ⊢ False`,
  -- which derives a match for the goal, `False`, `QED`

  -- Assume that the two premises are true:
  fun (hP : P) => 
    fun (hPimpFalse : P → False) => 

      -- Then apply `MP: (P → False), P ⊢ False` to derive `False`,
      -- which is a match for the goal, `QED`.
      (hPimpFalse hP : False) -- `MP: `

theorem double_neg_elim_attempt : ¬¬P → P := by
  -- Let's fully expand the double negation premise:
  -- `¬¬P`          =
  -- `(¬P → False)` =
  -- `((P → False) → False)`
  intro (hPremise : ((P → False) → False))
  -- There is no way in Lean to decouple the `P` 
  -- in the premise without converting to classical logical,
  -- where the `by_contra` tactic is allow.
  by_contra hPimpFalse : P → False
  have hFalse := hPremise hPimpFalse
  exact show False from hFalse

