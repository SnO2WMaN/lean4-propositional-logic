import PropositionalLogic.Notations
import PropositionalLogic.HilbertSystem.Definitions
import PropositionalLogic.HilbertSystem.HPM₀
import PropositionalLogic.HilbertSystem.HPM
import PropositionalLogic.HilbertSystem.HPJ

namespace PropositionalLogic.HilbertSystem

open Finset Notations HilbertSystem
attribute [-simp] union_assoc

class HPK
  (L : Type u) [DecidableEq L] [HilbertSystem L]
 [HasBot L] [HasArrow L] [HasLnot L] [HasLor L] [HasLand L] [HasLiff L]
 extends HPM L, HasDNE L

namespace HPK

variable
  {L : Type u} [DecidableEq L]
  [HasBot L] [HasArrow L] [HasLnot L] [HasLor L] [HasLand L] [HasLiff L]
  [HilbertSystem L] [HPK L]

open HilbertSystem HPM₀ HPM
open HasAxiomK HasMP HasDNE

instance : HasCon₃ L := ⟨HasCon₃.axiomCon₃⟩
instance : HasCon₄ L := ⟨HasCon₄.axiomCon₄⟩

instance : HasEFQ L where
  axiomEFQ Γ φ := by
    simp [deduction];
    have h1 : Γ ∪ {⊥'} ⊢ (⊥' : L) := by simp;
    have h2 : Γ ∪ {⊥'} ⊢ ((φ →' ⊥') →' ⊥') →' φ := by rw [←eqLnot, ←eqLnot]; apply axiomDNE;
    have h3 : Γ ∪ {⊥'} ⊢ (⊥' →' (φ →' ⊥') →' ⊥') := by apply axiomK;
    have h4 := MP h3 h1;
    have h5 := MP h2 h4;
    assumption;

instance : HasTND L where
  axiomTND Γ φ ψ := by admit

instance : HasCM₂ L := ⟨HasCM₂.axiomCM₂⟩

end HPK

variable
  (L : Type u) [DecidableEq L] [HilbertSystem L]
  [HasBot L] [HasArrow L] [HasLnot L] [HasLor L] [HasLand L] [HasLiff L]
in
theorem stronger : HPJ L → HPK L := by
  admit

end PropositionalLogic.HilbertSystem

