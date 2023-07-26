import PropositionalLogic.Notations
import PropositionalLogic.HilbertSystem.Definitions
import PropositionalLogic.HilbertSystem.HPM₀

namespace PropositionalLogic.HilbertSystem

open Finset Notations HilbertSystem
attribute [-simp] union_assoc

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

lemma EConj₁ {φ₁ φ₂ : L} : (Γ ⊢ (φ₁ ∧' φ₂)) → (Γ ⊢ φ₁) := by
  intro h;
  exact MP (axiomEConj₁ _ _ _) h;

lemma EConj₂ {φ₁ φ₂ : L} : (Γ ⊢ (φ₁ ∧' φ₂)) → (Γ ⊢ φ₂) := by
  intro h;
  exact MP (axiomEConj₂ _ _ _) h;

lemma lnc (φ : L) : (⊢ ¬'(φ ∧' ¬'φ)) := by
  simp [deduction];
  have s1 : {φ ∧' (φ →' ⊥')} ⊢ φ ∧' (φ →' ⊥') := context _ _ (by simp);
  have s2 : {φ ∧' (φ →' ⊥')} ⊢ (φ ∧' (φ →' ⊥') →' φ) := by apply axiomEConj₁;
  have s3 : {φ ∧' (φ →' ⊥')} ⊢ (φ ∧' (φ →' ⊥') →' (φ →' ⊥')) := by apply axiomEConj₂;
  have s4 := MP s2 s1;
  have s5 := MP s3 s1;
  have s6 := MP s5 s4;
  assumption;

lemma disjComm (φ ψ : L) : (⊢ (φ ∨' ψ) →' (ψ ∨' φ)) := by
  simp [deduction];
  have s1 : {φ ∨' ψ} ⊢ φ ∨' ψ := by simp;
  have s2 : {φ ∨' ψ} ⊢ φ →' (ψ ∨' φ) := by apply axiomIDisj₂;
  have s3 : {φ ∨' ψ} ⊢ ψ →' (ψ ∨' φ) := by apply axiomIDisj₁;
  have s5 := MP (EDisj s2 s3) s1;
  assumption;

lemma conjComm (φ ψ : L) : (⊢ (φ ∧' ψ) →' (ψ ∧' φ)) := by
  simp [deduction];
  have s1 : {φ ∧' ψ} ⊢ φ ∧' ψ := by simp;
  have s2 := EConj₂ s1;
  have s3 := EConj₁ s1;
  have s6 := IConj s2 s3;
  assumption;

lemma ELiff_mp (φ₁ φ₂ : L) : (Γ ⊢ φ₁ ↔' φ₂) → (Γ ⊢ φ₁ →' φ₂):= by
  simp [deduction];
  intro h;
  have s1 : Γ ∪ {φ₁} ⊢ φ₁ := by simp;
  have s2 : Γ ∪ {φ₁} ⊢ ((φ₁ →' φ₂) ∧' (φ₂ →' φ₁)) →' (φ₁ →' φ₂) := by apply axiomEConj₁;
  have s3 := weakenContext Γ (Γ ∪ {φ₁}) (by simp) h;
  have s4 := MP s2 s3;
  have s5 := MP s4 s1;
  assumption;

lemma ELiff_mpr' (φ₁ φ₂ : L) : (Γ ⊢ φ₁ ↔' φ₂) → (Γ ⊢ φ₂ →' φ₁):= by
  simp [deduction];
  intro h;
  have s1 : Γ ∪ {φ₂} ⊢ φ₂ := by simp;
  have s2 : Γ ∪ {φ₂} ⊢ ((φ₁ →' φ₂) ∧' (φ₂ →' φ₁)) →' (φ₂ →' φ₁) := by apply axiomEConj₂;
  have s3 := weakenContext Γ (Γ ∪ {φ₂}) (by simp) h;
  have s4 := MP s2 s3;
  have s5 := MP s4 s1;
  assumption;

lemma ILiff' (φ₁ φ₂ : L) : ((Γ ⊢ φ₁ →' φ₂) ∧ (Γ ⊢ φ₂ →' φ₁)) → (Γ ⊢ φ₁ ↔' φ₂) := by
  simp [And.intro, deduction];
  intro h1 h2;
  have s1 : Γ ⊢ ((φ₁ →' φ₂) →' (φ₂ →' φ₁) →' (φ₁ →' φ₂) ∧' (φ₂ →' φ₁)) := by apply axiomIConj;
  have s2 := MP s1 (deduction.mpr h1);
  have s3 := MP s2 (deduction.mpr h2);
  assumption;

lemma disjCommLiff (φ ψ : L) : (⊢ (φ ∨' ψ) ↔' (ψ ∨' φ)) := by
  apply ILiff';
  apply And.intro <;> simp [ disjComm];

lemma conjCommLiff (φ ψ : L) : (⊢ (φ ∧' ψ) ↔' (ψ ∧' φ)) := by
  apply ILiff';
  apply And.intro <;> simp [ conjComm];

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
  . simp [deduction];
    have h1 : {(φ →' ⊥') ∧' (ψ →' ⊥')} ∪ {φ ∨' ψ} ⊢ (φ →' ⊥') ∧' (ψ →' ⊥') := by simp;
    have h2 : {(φ →' ⊥') ∧' (ψ →' ⊥')} ∪ {φ ∨' ψ} ⊢ φ ∨' ψ := by simp;
    have h3 := (EDisj (EConj₁ h1) (EConj₂ h1));
    have h4 := MP h3 h2;
    assumption;

section Extended

instance [HasDNE L] : HasCon₃ L where
  axiomCon₃ Γ φ ψ := by
    simp only [deduction];
    have h1 : Γ ∪ {¬'φ →' ψ} ∪ {¬'ψ} ⊢ ¬'φ →' ψ := by simp;
    have h2 := MP (Con₁ _ _ _) h1;
    have h3 : Γ ∪ {¬'φ →' ψ} ∪ {¬'ψ} ⊢ ¬'ψ := by simp;
    have h4 := MP h2 h3;
    exact MP (HasDNE.axiomDNE _ _) h4

instance [HasCon₃ L] : HasDNE L where
  axiomDNE _ _ := MP (HasCon₃.axiomCon₃ _ _ _) (by simp);

instance [HasDNE L] : HasCon₄ L where
  axiomCon₄ Γ φ ψ := by
    simp only [deduction];
    have h1 : Γ ∪ {¬'φ →' ¬'ψ} ∪ {ψ} ⊢ ¬'φ →' ¬'ψ := by simp;
    have h2 := MP (Con₂ _ _ _) h1;
    have h3 : Γ ∪ {¬'φ →' ¬'ψ} ∪ {ψ} ⊢ ψ := by simp;
    have h4 := MP h2 h3;
    exact MP (HasDNE.axiomDNE _ _) h4

instance [HasCon₄ L] : HasDNE L where
  axiomDNE _ _ := MP (HasCon₄.axiomCon₄ _ _ _) (DNI _ _);

instance [HasLEM L] : HasCM₂ L where
  axiomCM₂ Γ φ := by
    simp only [deduction];
    have s1 : {(φ →' ⊥') →' φ} ⊢ φ ∨' ¬'φ := by apply HasLEM.axiomLEM;
    have s2 : {(φ →' ⊥') →' φ} ⊢ φ →' φ := by simp;
    have s3 : {(φ →' ⊥') →' φ} ⊢ ¬'φ →' φ := by simp;
    have s4 := MP (EDisj s2 s3) s1;
    exact weakenContext _ _ (by simp) s4

/-
  https://scrapbox.io/kokuritsukouen/%E6%8E%92%E4%B8%AD%E5%BE%8B%E3%81%AFHPM_+_CM%E2%82%82%E3%81%A7%E8%A8%BC%E6%98%8E%E5%8F%AF%E8%83%BD
-/
instance [HasCM₂ L] : HasLEM L where
  axiomLEM Γ φ := by
    have h1 := HasAxiomK.axiomK {φ ∨' ¬'φ →' ⊥'} (φ ∨' ¬'φ →' ⊥') φ;
    have h2 : {φ ∨' ¬'φ →' ⊥'} ⊢ φ ∨' ¬'φ →' ⊥' := by simp;
    have h3 := MP h1 h2;
    have h4 : {φ ∨' ¬'φ →' ⊥'} ⊢ φ →' (φ ∨' ¬'φ ) := by apply axiomIDisj₁;
    have h5 := HasAxiomS.axiomS {φ ∨' ¬'φ →' ⊥'} φ (φ ∨' ¬'φ ) ⊥';
    have h6 := MP h5 h3;
    have h7 := MP h6 h4;
    have h8 : {φ ∨' ¬'φ →' ⊥'} ⊢ (φ →' ⊥') →' (φ ∨' ¬'φ ) := by simp; apply axiomIDisj₂;
    have h9 := MP h8 h7;
    have h10 : ⊢ (φ ∨' ¬'φ →' ⊥') →' (φ ∨' ¬'φ) := deduction.mpr h9;
    have h11 : ⊢ (((φ ∨' ¬'φ) →' ⊥') →' (φ ∨' ¬'φ)) →' (φ ∨' ¬'φ) := by rw [←eqLnot]; apply HasCM₂.axiomCM₂
    have h12 := MP h11 h10;
    exact weakenContext _ _ (by simp) h12;

instance [HasTND L] : HasCM₂ L where
  axiomCM₂ Γ φ := by
    simp only [deduction];
    have s1 : {(φ →' ⊥') →' φ} ⊢ ¬'φ →' φ := by simp;
    have s2 : {(φ →' ⊥') →' φ} ⊢ (φ →' φ) →' (¬'φ →' φ) →' φ := by apply HasTND.axiomTND;
    have s3 := MP s2 (by simp);
    have s4 := MP s3 s1;
    exact weakenContext _ _ (by simp) s4

instance [HasCM₂ L] : HasTND L where
  axiomTND Γ φ ψ := by
    admit

instance [HasPeirceLaw L] : HasCM₂ L where
  axiomCM₂ Γ φ := by
    simp [eqLnot];
    exact HasPeirceLaw.axiomPeirceLaw Γ φ ⊥';

instance [HasTarskiLaw L] : HasLEM L where
  axiomLEM Γ φ := by
    simp [eqLnot];
    exact HasTarskiLaw.axiomTarskiLaw Γ φ ⊥';

instance [HasTarskiLaw L] : HasPeirceLaw L where
  axiomPeirceLaw Γ φ ψ := by
    simp [deduction];
    exact MP (EDisj (by simp) (by simp)) (HasTarskiLaw.axiomTarskiLaw _ φ ψ);

instance [HasPeirceLaw L] : HasTarskiLaw L where
  axiomTarskiLaw Γ φ ψ := by
    admit

end Extended

end HPM

variable
  (L : Type u) [DecidableEq L] [HilbertSystem L]
  [HasBot L] [HasArrow L] [HasLnot L] [HasLor L] [HasLand L] [HasLiff L]
in
theorem HPM.strongerThanHPM₀ {Γ : Context L} {φ : L}:
  (HPM₀ L → @HilbertSystem.provable L _ Γ φ) → (HPM L → @HilbertSystem.provable L _ Γ φ) := by
  admit

end PropositionalLogic.HilbertSystem
