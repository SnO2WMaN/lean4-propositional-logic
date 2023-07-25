import Lean
import Mathlib.Data.Set.Basic

namespace PropositionalLogic.Notation

variable (α : Type u)

class HasBot where bot : α
notation "⊥'" => HasBot.bot
attribute [match_pattern] HasBot.bot

class HasArrow where arrow : α → α → α
infixr:61 " →' " => HasArrow.arrow
attribute [match_pattern] HasArrow.arrow

class HasMinimalLogicSymbols extends HasBot α, HasArrow α

section lnot

class HasLnot where lnot : α → α
prefix:max "¬'" => HasLnot.lnot

-- def HasMinimalLogicSymbols.lnot [HasMinimalLogicSymbols α] (p : α) := p →' ⊥'
-- instance [HasMinimalLogicSymbols α] : HasLnot α where lnot := HasMinimalLogicSymbols.lnot α

end lnot

section top

class HasTop where top : α
notation "⊤'" => HasTop.top

-- def HasMinimalLogicSymbols.top [HasMinimalLogicSymbols α] : α := ¬'⊥'
-- instance [HasMinimalLogicSymbols α] : HasTop α where top := HasMinimalLogicSymbols.top α

end top

section lor

class HasLor where lor : α → α → α
infixl:62 " ∨' " => HasLor.lor

-- def HasMinimalLogicSymbols.lor [HasMinimalLogicSymbols α] (p q : α) : α := (¬'p) →' q
-- instance [HasMinimalLogicSymbols α] : HasLor α where lor := HasMinimalLogicSymbols.lor α

end lor

section land

class HasLand where land : α → α → α
infixl:63 " ∧' " => HasLand.land

-- def HasMinimalLogicSymbols.land [HasMinimalLogicSymbols α] (p q : α) : α := ¬'((¬'p : α) ∨' ¬'q)
-- instance [HasMinimalLogicSymbols α] : HasLand α where land := HasMinimalLogicSymbols.land α

end land

class HasLogicSymbols (α : Type u) extends
  HasTop α, HasBot α, HasLnot α, HasLand α, HasLor α, HasArrow α

section liff

class HasLiff where liff : α → α → α
infixl:60 " ↔' " => HasLiff.liff

-- def HasLogicSymbols.liff [HasLogicSymbols α] (p q : α) : α := (p →' q) ∧' (q →' p)
-- instance [HasLogicSymbols α] : HasLand α where land := HasLogicSymbols.liff α

end liff


/-
class HasTurnstile (α : Sort _) (β : Sort _) where turnstile : Set α → α → β

infix:10 " ⊢ " => HasTurnstile.turnstile
-/

end PropositionalLogic.Notation
