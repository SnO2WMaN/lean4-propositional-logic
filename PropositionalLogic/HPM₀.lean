import Mathlib.Data.Finset.Basic
import PropositionalLogic.Notation
import PropositionalLogic.HilbertSystem

attribute [simp] Finset.subset_union_left Finset.subset_union_right
attribute [-simp] Finset.union_assoc

namespace PropositionalLogic

open Finset Notation HilbertSystem

class HPM₀
  (L : Type u)
  [DecidableEq L] [HilbertSystem L] [HasArrow L] [HasBot L] [HasLnot L]
  extends HasAxiomS L, HasAxiomK L, HasMP L where
  eqLnot (φ : L) : (¬'φ = φ →' ⊥')

attribute [simp] HPM₀.eqLnot

namespace HPM₀

variable
  {L : Type u} [DecidableEq L]
  [HasArrow L] [HasBot L] [HasLnot L]
  [HilbertSystem L] [HPM₀ L]

open HilbertSystem HasAxiomS HasAxiomK HasMP

@[simp]
lemma weakenImp (φ : L) : (Γ ⊢ ψ) → (Γ ⊢ (φ →' ψ)) := by exact λ h => MP (axiomK _ ψ φ) h;

lemma weakenContext (Γ Δ : Context L) (hs : Γ ⊆ Δ) : (Γ ⊢ φ) → (Δ ⊢ φ) := by sorry

lemma weakenContext' (Γ : Context L) : (⊢ φ) → (Γ ⊢ φ) := weakenContext ∅ Γ (by simp)
instance (Γ : Context L) : Coe (⊢ φ) (Γ ⊢ φ) := ⟨weakenContext' Γ⟩

lemma id_imp' (φ : L) : ⊢ (φ →' φ) := by
  have s1 : ⊢ (φ →' (φ →' φ) →' φ) := by apply axiomK;
  have s2 : ⊢ ((φ →' (φ →' φ) →' φ) →' (φ →' φ →' φ) →' φ →' φ) := by apply axiomS;
  have s3 : ⊢ ((φ →' φ →' φ) →' φ →' φ) := MP s2 s1;
  have s4 : ⊢ (φ →' φ →' φ) := by apply axiomK;
  have s5 : ⊢ (φ →' φ) := MP s3 s4;
  assumption;

@[simp]
lemma id_imp (φ : L) : Γ ⊢ (φ →' φ) := ↑(HPM₀.id_imp' φ)

@[simp]
lemma id (φ : L) : {φ} ⊢ φ := context _ _ (by simp)

theorem deduction {Γ : Context L} {φ ψ : L} : (Γ ⊢ (φ →' ψ)) ↔ ((Γ ∪ {φ}) ⊢ ψ) := by
  apply Iff.intro
  . intro h;
    have h1 : (Γ ∪ {φ}) ⊢ (φ →' ψ) := weakenContext Γ (Γ ∪ {φ}) (subset_union_left _ _) h;
    have h2 := context (Γ ∪ {φ}) φ (by simp);
    exact MP h1 h2;
  . admit

variable (Γ : Context L) (φ ψ χ : L)

theorem commAxiomK : (Γ ⊢ φ) → (Γ ⊢ (φ →' ψ) →' φ) := by
  intro h;
  simp [deduction];

theorem DNI : (Γ ⊢ (φ →' ¬'¬'φ)) := by
  simp [deduction];
  have s1 : Γ ∪ {φ} ∪ {φ →' ⊥'} ⊢ φ := by simp;
  have s2 : Γ ∪ {φ} ∪ {φ →' ⊥'} ⊢ φ →' ⊥' := by simp;
  have s3 := MP s2 s1;
  assumption;

theorem CM₁ : (Γ ⊢ (φ →' ¬'φ) →' ¬'φ) := by
  simp [deduction];
  have s1 : Γ ∪ {φ →' φ →' ⊥'} ∪ {φ} ⊢ φ →' φ →' ⊥' := by simp;
  have s2 : Γ ∪ {φ →' φ →' ⊥'} ∪ {φ} ⊢ φ := by simp;
  have s3 := MP s1 s2;
  have s4 := MP s3 s2;
  assumption;

theorem RAA : (Γ ⊢ (φ →' ⊥') →' ¬'φ) := by simp;

theorem Con₁ : (Γ ⊢ (φ →' ψ) →' (¬'ψ →' ¬'φ)) := by
  simp [deduction];
  have s1 : Γ ∪ {φ →' ψ} ∪ {ψ →' ⊥'} ∪ {φ} ⊢ φ := by simp;
  have s2 : Γ ∪ {φ →' ψ} ∪ {ψ →' ⊥'} ∪ {φ} ⊢ φ →' ψ := by simp;
  have s3 : Γ ∪ {φ →' ψ} ∪ {ψ →' ⊥'} ∪ {φ} ⊢ ψ →' ⊥' := by simp;
  have s4 := MP s2 s1;
  have s5 := MP s3 s4;
  assumption;

theorem Con₂ : (Γ ⊢ (φ →' ¬'ψ) →' (ψ →' ¬'φ)) := by
  simp [deduction];
  have s1 : Γ ∪ {φ →' ψ →' ⊥'} ∪ {ψ} ∪ {φ} ⊢ φ := by simp;
  have s2 : Γ ∪ {φ →' ψ →' ⊥'} ∪ {ψ} ∪ {φ} ⊢ ψ := by simp;
  have s3 : Γ ∪ {φ →' ψ →' ⊥'} ∪ {ψ} ∪ {φ} ⊢ φ →' ψ →' ⊥' := by simp;
  have s4 := MP s3 s1;
  have s5 := MP s4 s2;
  assumption;

end HPM₀

end PropositionalLogic
