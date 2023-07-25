import PropositionalLogic.Notation
import PropositionalLogic.HilbertSystem
import PropositionalLogic.HPM₀

namespace PropositionalLogic

open Finset Notation HilbertSystem

class HPM
  (L : Type u) [DecidableEq L]
  [HasBot L] [HasArrow L] [HasLnot L] [HasLor L] [HasLand L] [HasLiff L]
  [HilbertSystem L]
  extends HPM₀ L, HasIDisj L, HasEDisj L, HasIConj L, HasEConj L where
  eqLiff (φ ψ : L) : ((φ ↔' ψ) = (φ →' ψ) ∧' (ψ →' φ))

attribute [simp] HPM.eqLiff

namespace HPM

variable
  {L : Type u} [DecidableEq L]
  [HasBot L] [HasArrow L] [HasLnot L] [HasLor L] [HasLand L] [HasLiff L]
  [HilbertSystem L] [HPM L]

open HilbertSystem HasAxiomS HasAxiomK HasMP HasIDisj HasEDisj HasIConj HasEConj
open HPM₀

lemma IDisj₁ {φ₁ φ₂ : L} : (Γ ⊢ φ₁) → (Γ ⊢ (φ₁ ∨' φ₂)) := by
  intro h;
  exact MP (axiomIDisj₁ _ _ _) h

lemma IDisj₂ {φ₁ φ₂ : L} : (Γ ⊢ φ₂) → (Γ ⊢ (φ₁ ∨' φ₂)) := by
  intro h;
  exact MP (axiomIDisj₂ _ _ _) h

lemma EDisj {φ ψ : L} : (Γ ⊢ (φ →' χ)) → (Γ ⊢ (ψ →' χ)) → (Γ ⊢ ((φ ∨' ψ) →' χ)) := by
  intro hφ hψ;
  exact MP (MP (axiomEDisj _ _ _ _) hφ) hψ;

lemma IConj {φ ψ : L} : (Γ ⊢ φ) → (Γ ⊢ ψ) → (Γ ⊢ (φ ∧' ψ)) := by
  intro hφ hψ;
  exact MP (MP (axiomIConj _ _ _) hφ) hψ;

lemma EConj₁ {φ ψ : L} : (Γ ⊢ (φ ∧' ψ)) → (Γ ⊢ φ) := by
  intro h;
  exact MP (axiomEConj₁ _ _ _) h;

lemma EConj₂ {φ ψ : L} : (Γ ⊢ (φ ∧' ψ)) → (Γ ⊢ ψ) := by
  intro h;
  exact MP (axiomEConj₂ _ _ _) h;

lemma lnc (φ : L) : (⊢ ¬'(φ ∧' ¬'φ)) := by
  simp;
  have s1 : {φ ∧' (φ →' ⊥')} ⊢ φ ∧' (φ →' ⊥') := context _ _ (by simp);
  have s2 : {φ ∧' (φ →' ⊥')} ⊢ (φ ∧' (φ →' ⊥') →' φ) := by apply axiomEConj₁;
  have s3 : {φ ∧' (φ →' ⊥')} ⊢ (φ ∧' (φ →' ⊥') →' (φ →' ⊥')) := by apply axiomEConj₂;
  have s4 := MP s2 s1;
  have s5 := MP s3 s1;
  have s6 := MP s5 s4;
  assumption;

lemma disjComm (φ ψ : L) : (⊢ (φ ∨' ψ) →' (ψ ∨' φ)) := by
  simp;
  have s1 : {φ ∨' ψ} ⊢ φ ∨' ψ := by simp;
  have s2 : {φ ∨' ψ} ⊢ φ →' (ψ ∨' φ) := by apply axiomIDisj₂;
  have s3 : {φ ∨' ψ} ⊢ ψ →' (ψ ∨' φ) := by apply axiomIDisj₁;
  have s5 := MP (EDisj s2 s3) s1;
  assumption;

lemma conjComm (φ ψ : L) : (⊢ (φ ∧' ψ) →' (ψ ∧' φ)) := by
  simp;
  have s1 : {φ ∧' ψ} ⊢ φ ∧' ψ := by simp;
  have s2 := EConj₂ s1;
  have s3 := EConj₁ s1;
  have s6 := IConj s2 s3;
  assumption;

lemma ELiff_mp (φ₁ φ₂ : L) : (Γ ⊢ φ₁ ↔' φ₂) → (Γ ⊢ φ₁ →' φ₂):= by
  simp;
  intro h;
  have s1 : Γ ∪ {φ₁} ⊢ φ₁ := by simp;
  have s2 : Γ ∪ {φ₁} ⊢ ((φ₁ →' φ₂) ∧' (φ₂ →' φ₁)) →' (φ₁ →' φ₂) := by apply axiomEConj₁;
  have s3 := weakenContext Γ (Γ ∪ {φ₁}) (by simp) h;
  have s4 := MP s2 s3;
  have s5 := MP s4 s1;
  assumption;

lemma ELiff_mpr' (φ₁ φ₂ : L) : (Γ ⊢ φ₁ ↔' φ₂) → (Γ ⊢ φ₂ →' φ₁):= by
  simp;
  intro h;
  have s1 : Γ ∪ {φ₂} ⊢ φ₂ := by simp;
  have s2 : Γ ∪ {φ₂} ⊢ ((φ₁ →' φ₂) ∧' (φ₂ →' φ₁)) →' (φ₂ →' φ₁) := by apply axiomEConj₂;
  have s3 := weakenContext Γ (Γ ∪ {φ₂}) (by simp) h;
  have s4 := MP s2 s3;
  have s5 := MP s4 s1;
  assumption;

lemma ILiff' (φ₁ φ₂ : L) : ((Γ ⊢ φ₁ →' φ₂) ∧ (Γ ⊢ φ₂ →' φ₁)) → (Γ ⊢ φ₁ ↔' φ₂) := by
  simp [And.intro];
  intro h1 h2;
  have s1 : Γ ⊢ ((φ₁ →' φ₂) →' (φ₂ →' φ₁) →' (φ₁ →' φ₂) ∧' (φ₂ →' φ₁)) := by apply axiomIConj;
  have s2 := MP s1 (deduction.mpr h1);
  have s3 := MP s2 (deduction.mpr h2);
  assumption;

lemma disjCommLiff (φ ψ : L) : (⊢ (φ ∨' ψ) ↔' (ψ ∨' φ)) := by
  apply ILiff';
  apply And.intro <;> simp [-deduction, disjComm];

lemma conjCommLiff (φ ψ : L) : (⊢ (φ ∧' ψ) ↔' (ψ ∧' φ)) := by
  apply ILiff';
  apply And.intro <;> simp [-deduction, conjComm];

lemma distDisj (φ ψ χ : L) : (⊢ (φ ∨' (ψ ∧' χ)) ↔' ((φ ∨' ψ) ∧' (φ ∨' χ))) := by
  apply ILiff';
  simp;
  apply And.intro;
  . have h1 : {φ ∨' ψ ∧' χ} ⊢ (φ ∨' ψ ∧' χ) := by simp;
    have h2 := axiomEConj₁ {φ ∨' ψ ∧' χ} (φ ∧' ψ) χ;
    have h3 := axiomEConj₂ {φ ∨' ψ ∧' χ} (φ ∧' ψ) χ;
    sorry
  . sorry

lemma distConj (φ ψ χ : L) : (⊢ (φ ∧' (ψ ∨' χ)) ↔' ((φ ∧' ψ) ∨' (φ ∧' χ))) := by
  apply ILiff';
  simp;
  apply And.intro;
  . have h1 : {φ ∧' ψ ∨' φ ∧' χ} ⊢ φ ∧' ψ ∨' φ ∧' χ := by simp;
    have h2 := axiomEDisj {φ ∧' ψ ∨' φ ∧' χ} φ (ψ ∨' χ) ψ;
    have h3 := axiomEDisj {φ ∧' ψ ∨' φ ∧' χ} φ (ψ ∨' χ) χ;
    -- have h6 := axiomEDisj {φ ∧' ψ ∨' φ ∧' χ} φ (ψ ∨' χ) χ;
    sorry
  . have h1 : {φ ∧' ψ ∨' φ ∧' χ} ⊢ φ ∧' ψ ∨' φ ∧' χ := by simp;
    have h5 := MP (EDisj (axiomEConj₁ _ _ _) (axiomEConj₁ _ _ _)) h1;
    sorry

  /-
  . have h1 : {φ ∧' (ψ ∨' χ)} ⊢ φ ∧' (ψ ∨' χ) := by simp;
    have h2 := axiomEConj₁ {φ ∧' (ψ ∨' χ)} φ (ψ ∨' χ);
    have h3 := axiomEConj₂ {φ ∧' (ψ ∨' χ)} φ (ψ ∨' χ);
    have h4 := MP h2 h1;
    have h5 := MP h3 h1;
    -- have h6 := axiomEDisj {φ ∧' (ψ ∨' χ)} φ (ψ ∨' χ) χ;
    sorry
  . have h1 : {φ ∧' ψ ∨' φ ∧' χ} ⊢ φ ∧' ψ ∨' φ ∧' χ := by simp;

    have h2 : {φ ∧' ψ ∨' φ ∧' χ} ⊢ ((φ ∧' ψ) →' φ) →' ((φ ∧' χ) →' φ) →' (((φ ∧' ψ) ∨' (φ ∧' χ)) →' φ) := by apply axiomEDisj;
    have h3 : {φ ∧' ψ ∨' φ ∧' χ} ⊢ (φ ∧' ψ) →' φ := by apply axiomEConj₁;
    have h4 : {φ ∧' ψ ∨' φ ∧' χ} ⊢ (φ ∧' χ) →' φ := by apply axiomEConj₁;
    have h5 := MP (MP (MP h2 h3) h4) h1;

    have h6 : {φ ∧' ψ ∨' φ ∧' χ} ⊢ ψ →' (ψ ∨' χ) := by apply axiomIDisj₁;
    have h7 : {φ ∧' ψ ∨' φ ∧' χ} ⊢ χ →' (ψ ∨' χ) := by apply axiomIDisj₂;
    have h8 : {φ ∧' ψ ∨' φ ∧' χ} ⊢ ((φ ∧' ψ) →' (ψ ∨' χ)) →' ((φ ∧' χ) →' (ψ ∨' χ)) →' (((φ ∧' ψ) ∨' (φ ∧' χ)) →' (ψ ∨' χ)) := by apply axiomEDisj;


    have h6 := axiomIDisj₁ {φ ∧' ψ ∨' φ ∧' χ} φ (ψ ∨' χ);
  -/

lemma duMorganConj (φ ψ : L) : (⊢ ¬'(φ ∨' ψ) ↔' (¬'φ ∧' ¬'ψ)) := by
  apply ILiff';
  apply And.intro;
  . sorry
  . simp;
    have h1 : {(φ →' ⊥') ∧' (ψ →' ⊥')} ∪ {φ ∨' ψ} ⊢ (φ →' ⊥') ∧' (ψ →' ⊥') := by simp;
    have h2 : {(φ →' ⊥') ∧' (ψ →' ⊥')} ∪ {φ ∨' ψ} ⊢ φ ∨' ψ := by simp;
    have h3 := (EDisj (EConj₁ h1) (EConj₂ h1));
    have h4 := MP h3 h2;
    assumption;

section Extended

open HasLEM in
instance [HasLEM L] : HasCM₂ L where
  axiomCM₂ Γ φ := by
    simp;
    have s1 : {(φ →' ⊥') →' φ} ⊢ φ ∨' ¬'φ := by apply axiomLEM;
    have s2 : {(φ →' ⊥') →' φ} ⊢ φ →' φ := by simp;
    have s3 : {(φ →' ⊥') →' φ} ⊢ ¬'φ →' φ := by simp;
    have s4 := MP (EDisj s2 s3) s1;
    exact weakenContext _ _ (by simp) s4

open HasCM₂ in
instance [HasCM₂ L] : HasLEM L where
  axiomLEM Γ φ := by admit

open HasTND in
instance [HasTND L] : HasCM₂ L where
  axiomCM₂ Γ φ := by
    simp;
    have s1 : {(φ →' ⊥') →' φ} ⊢ ¬'φ →' φ := by simp;
    have s2 : {(φ →' ⊥') →' φ} ⊢ (φ →' φ) →' (¬'φ →' φ) →' φ := by apply axiomTND;
    have s3 := MP s2 (by simp);
    have s4 := MP s3 s1;
    exact weakenContext _ _ (by simp) s4

open HasCM₂ in
instance [HasCM₂ L] : HasTND L where
  axiomTND Γ φ := by admit

open HasPeirceLaw in
instance [HasPeirceLaw L] : HasCM₂ L where
  axiomCM₂ Γ φ := by
    simp [-deduction, eqLnot];
    exact axiomPeirceLaw Γ φ ⊥';

open HasTarskiLaw in
instance [HasTarskiLaw L] : HasLEM L where
  axiomLEM Γ φ := by
    simp [-deduction, eqLnot];
    exact axiomTarskiLaw Γ φ ⊥';

open HasPeirceLaw in
instance [HasPeirceLaw L] : HasTarskiLaw L where
  axiomTarskiLaw Γ φ ψ := by
    admit

end Extended

end HPM

end PropositionalLogic
