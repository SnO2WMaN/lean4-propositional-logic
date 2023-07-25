import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import PropositionalLogic.Notation

attribute [simp] Finset.subset_union_left Finset.subset_union_right
attribute [-simp] Finset.union_assoc

namespace PropositionalLogic

open Finset Notation

variable (L : Type u) [DecidableEq L] [HasMinimalLogicSymbols L]

class HilbertSystem where
  provable : Finset L → L → Prop
  context Γ φ : φ ∈ Γ → provable Γ φ

abbrev Context L := Finset L

attribute [match_pattern] HilbertSystem.provable HilbertSystem.context
attribute [simp] HilbertSystem.context

notation:10 Γ " ⊢ " φ => HilbertSystem.provable Γ φ
notation:11 "⊢ " φ => ∅ ⊢ φ

variable (L : Type u) [DecidableEq L] [HilbertSystem L]

class HasAxiomS [HasArrow L]  where
  axiomS (Γ : Context L) φ ψ χ : Γ ⊢ ((φ →' (ψ →' χ)) →' ((φ →' ψ) →' (φ →' χ)))

class HasAxiomK [HasArrow L] where
  axiomK (Γ : Context L) φ ψ : Γ ⊢ (φ →' (ψ →' φ))

class HasMP [HasArrow L] where
  MP {Γ : Context L} {φ ψ} : (Γ ⊢ (φ →' ψ)) → (Γ ⊢ φ) → (Γ ⊢ ψ)

class HasIDisj [HasArrow L] [HasLor L] where
  axiomIDisj₁ (Γ : Context L) φ₁ φ₂ : Γ ⊢ (φ₁ →' φ₁ ∨' φ₂)
  axiomIDisj₂ (Γ : Context L) φ₁ φ₂ : Γ ⊢ (φ₂ →' φ₁ ∨' φ₂)

class HasEDisj [HasArrow L] [HasLor L] where
  axiomEDisj (Γ : Context L) φ ψ χ : Γ ⊢ ((φ →' χ) →' (ψ →' χ) →' (φ ∨' ψ →' χ))

class HasIConj [HasArrow L] [HasLand L] where
  axiomIConj (Γ : Context L) φ ψ : Γ ⊢ (φ →' ψ →' φ ∧' ψ)

class HasEConj [HasArrow L] [HasLand L]  where
  axiomEConj₁ (Γ : Context L) φ₁ φ₂ : Γ ⊢ (φ₁ ∧' φ₂ →' φ₁)
  axiomEConj₂ (Γ : Context L) φ₁ φ₂ : Γ ⊢ (φ₁ ∧' φ₂ →' φ₂)

class HasEFQ [HasArrow L] [HasBot L] where
  axiomEFQ (Γ : Context L) φ : Γ ⊢ (⊥' →' φ)

class HasCon₃ [HasArrow L] [HasLnot L] where
  axiomCon₃ (Γ : Context L) φ : Γ ⊢ (¬'φ →' ψ) →' (¬'ψ →' φ)

class HasCon₄ [HasArrow L] [HasLnot L] where
  axiomCon₄ (Γ : Context L) φ : Γ ⊢ (¬'φ →' ¬'ψ) →' (ψ →' φ)

class HasDNE [HasArrow L] [HasLnot L] where
  axiomDNE (Γ : Context L) φ : Γ ⊢ (¬'¬'φ →' φ)

class HasCM₂ [HasArrow L] [HasLnot L] [HasLor L] where
  axiomCM₂ (Γ : Context L) φ : Γ ⊢ (¬'φ →' φ) →' φ

class HasLEM [HasArrow L] [HasLnot L] [HasLor L] where
  axiomLEM (Γ : Context L) φ : Γ ⊢ (φ ∨' ¬'φ)

class HasTND [HasArrow L] [HasLnot L] [HasLor L] where
  axiomTND (Γ : Context L) φ ψ : Γ ⊢ (φ →' ψ) →' (¬'φ →' ψ) →' ψ

class HasPeirceLaw [HasArrow L] where
  axiomPeirceLaw (Γ : Context L) φ ψ : Γ ⊢ (((φ →' ψ) →' φ) →' φ)

class HasTarskiLaw [HasArrow L] [HasLor L] where
  axiomTarskiLaw (Γ : Context L) φ ψ : Γ ⊢  φ ∨' (φ →' ψ)

lemma insertEmpty {φ : L} : ({φ} ⊢ ψ) → (∅ ∪ {φ} ⊢ ψ) := by simp
instance {φ : L} : Coe ({φ} ⊢ ψ) (∅ ∪ {φ} ⊢ ψ) := ⟨by simp⟩

end PropositionalLogic
