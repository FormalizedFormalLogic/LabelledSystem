import LabelledSystem.Gentzen.ReplaceLabel

lemma Multiset.map_id_domain {s : Multiset α} (hf : ∀ a ∈ s, f a = a) : s.map f = s := by
  rw [Multiset.map_congr rfl hf];
  exact Multiset.map_id' s

namespace LO.Modal.Labelled.Gentzen

open SequentPart
open DerivationWithHeight

noncomputable def wkFmlLₕAux (d : ⊢ᵍ[k] S) : ⊢ᵍ[k] ⟨(x ∶ φ) ::ₘ S.Γ.fmls, S.Γ.rels⟩ ⟹ S.Δ := by
  obtain ⟨d, kh⟩ := d;
  induction d generalizing k x with
  | initAtom y a => exact initAtomₕ' y a (by simp) (by simp);
  | initBot y => exact initBotₕ' y (by simp);
  | @impR S y ψ χ d ih =>
    by_cases k = 0;
    . simp at kh; omega;
    . suffices ⊢ᵍ[k]
        ⟨(x ∶ φ) ::ₘ S.Γ.fmls, S.Γ.rels⟩ ⟹ ⟨(y ∶ ψ ➝ χ) ::ₘ S.Δ.fmls, S.Δ.rels⟩
        by simpa;
      have := impRₕ
        (Γ := ⟨(x ∶ φ) ::ₘ S.Γ.fmls, S.Γ.rels⟩)
        (Δ := S.Δ)
        (x := y) (φ := ψ) (ψ := χ) (h := (k - 1)) ?_;
      simpa [(show k - 1 + 1 = k by omega)] using this;
      . exact exchangeFmlLₕ $ ih $ by simp at kh; omega;
  | @impL S y ψ ξ dψ dξ ihψ ihξ =>
    by_cases k = 0;
    . simp at kh; omega;
    . suffices ⊢ᵍ[k]
        (⟨(x ∶ φ) ::ₘ (y ∶ ψ ➝ ξ) ::ₘ S.Γ.fmls, S.Γ.rels⟩ ⟹ S.Δ)
        by simpa;
      have := exchangeFmlLₕ $ @impLₕ
        (Γ := ⟨(x ∶ φ) ::ₘ S.Γ.fmls, S.Γ.rels⟩)
        (Δ := S.Δ)
        (x := y) (φ := ψ) (ψ := ξ) (k₁ := (k - 1)) (k₂ := (k - 1)) ?_ ?_;
      simpa [(show k - 1 + 1 = k by omega)] using this;
      . exact ihψ (by simp at kh; omega);
      . exact exchangeFmlLₕ $ ihξ $ by simp at kh; omega;
  | @boxL S y z ψ d ih =>
    by_cases k = 0;
    . simp at kh; omega;
    . suffices ⊢ᵍ[k]
        (⟨(x ∶ φ) ::ₘ (y ∶ □ψ) ::ₘ S.Γ.fmls, (y, z) ::ₘ S.Γ.rels⟩ ⟹ S.Δ)
        by simpa;
      have := @boxLₕ
        (Γ := ⟨(x ∶ φ) ::ₘ S.Γ.fmls, S.Γ.rels⟩)
        (Δ := S.Δ)
        (x := y) (y := z) (φ := ψ) (k := k - 1) ?_;
      apply exchangeFmlLₕ (Γ := ⟨S.Γ.fmls, (y, z) ::ₘ S.Γ.rels⟩);
      simpa [(show k - 1 + 1 = k by omega)] using this;
      . apply exchangeFml₃Lₕ (Γ := ⟨S.Γ.fmls, (y, z) ::ₘ S.Γ.rels⟩);
        exact ih $ by simp at kh; omega;
  | @boxR S y z ψ hyz hΓz hΔz d ih =>
    by_cases k = 0;
    . simp at kh; omega;
    . suffices ⊢ᵍ[k]
        (⟨(x ∶ φ) ::ₘ S.Γ.fmls, S.Γ.rels⟩ ⟹ ⟨(y ∶ □ψ) ::ₘ S.Δ.fmls, S.Δ.rels⟩)
        by simpa;
      by_cases hzx : z = x;
      . subst hzx;
        let w : Label := ((⟨(z ∶ φ) ::ₘ S.Γ.fmls, S.Γ.rels⟩) ⟹ S.Δ).getFreshLabel;
        have := @boxRₕ
          (Γ := ⟨(w ∶ φ) ::ₘ S.Γ.fmls, S.Γ.rels⟩)
          (Δ := S.Δ)
          (x := y) (y := z) (φ := ψ) (h := k - 1) hyz ?_ ?_ ?_;
        have := @replaceLabelₕ (Γ := ⟨(w ∶ φ) ::ₘ S.Γ.fmls, S.Γ.rels⟩) (Δ := ⟨(y ∶ □ψ) ::ₘ S.Δ.fmls, S.Δ.rels⟩) _ this (w ↦ z);
        have e₁ : S.Γ.fmls.map (.labelReplace (w ↦ z)) = S.Γ.fmls := by
          apply Multiset.map_id_domain;
          intro ⟨l, ξ⟩ hlξ;
          apply LabelledFormula.labelReplace_specific_not;
          rintro rfl;
          have : (w ∶ ξ) ∉ S.Γ.fmls := not_include_labelledFml_of_isFreshLabel ?_ ξ;
          contradiction;
          apply getFreshLabel_mono (Δ := ⟨(w ∶ φ) ::ₘ S.Γ.fmls, S.Γ.rels⟩);
          . simp [Multiset.subset_cons];
          . rfl;
        have e₂ : S.Δ.fmls.map (.labelReplace (w ↦ z)) = S.Δ.fmls := by
          apply Multiset.map_id_domain;
          intro ⟨l, ξ⟩ hlξ;
          apply LabelledFormula.labelReplace_specific_not;
          rintro rfl;
          have : (w ∶ ξ) ∉ S.Δ.fmls := not_include_labelledFml_of_isFreshLabel ?_ ξ;
          contradiction;
          exact Sequent.getFreshLabel_isFreshLabel₂;
        have e₃ : S.Γ.rels.map (.labelReplace (w ↦ z)) = S.Γ.rels := by
          apply Multiset.map_id_domain;
          intro ⟨l₁, l₂⟩ hl;
          apply LabelTerm.labelReplace_specific_not_both;
          . rintro rfl;
            have : (w, l₂) ∉ S.Γ.rels := not_include_relTerm_of_isFreshLabel₁ ?_ l₂;
            contradiction;
            exact Sequent.getFreshLabel_isFreshLabel₁;
          . rintro rfl;
            have : (l₁, w) ∉ S.Γ.rels := not_include_relTerm_of_isFreshLabel₂ ?_ l₁;
            contradiction;
            exact Sequent.getFreshLabel_isFreshLabel₁;
        have e₄ : S.Δ.rels.map (.labelReplace (w ↦ z)) = S.Δ.rels := by
          apply Multiset.map_id_domain;
          intro ⟨l₁, l₂⟩ hl;
          apply LabelTerm.labelReplace_specific_not_both;
          . rintro rfl;
            have : (w, l₂) ∉ S.Δ.rels := not_include_relTerm_of_isFreshLabel₁ ?_ l₂;
            contradiction;
            exact Sequent.getFreshLabel_isFreshLabel₂;
          . rintro rfl;
            have : (l₁, w) ∉ S.Δ.rels := not_include_relTerm_of_isFreshLabel₂ ?_ l₁;
            contradiction;
            exact Sequent.getFreshLabel_isFreshLabel₂;
        have e₅ : (y ∶ □ψ)⟦w ↦ z⟧ = (y ∶ □ψ) := LabelledFormula.labelReplace_specific_not $ by
          sorry;
        simpa [
          e₁,
          e₂,
          e₃,
          e₄,
          e₅,
          (show k - 1 + 1 = k by omega)
        ] using this;
        . refine ⟨?_, ?_, ?_⟩;
          . suffices z ≠ w ∧ ∀ x ∈ S.Γ.fmls, ¬x.label = z by simpa;
            constructor;
            . apply @SequentPart.getFreshLabel_ne ({ fmls := (z ∶ φ) ::ₘ S.Γ.fmls, rels := S.Γ.rels }) z φ (by simp) |>.symm;
            . rintro ⟨w, ψ⟩ h rfl;
              have := not_include_labelledFml_of_isFreshLabel hΓz ψ;
              contradiction;
          . exact hΓz.2.1;
          . exact hΓz.2.2;
        . exact hΔz;
        . simpa using @ih (k - 1) w (by simp at kh; omega);
      . have := @boxRₕ
          (Γ := ⟨(x ∶ φ) ::ₘ S.Γ.fmls, S.Γ.rels⟩)
          (Δ := ⟨S.Δ.fmls, S.Δ.rels⟩)
          (x := y) (y := z) (φ := ψ) (h := k - 1) hyz ?_ hΔz ?_;
        simpa [(show k - 1 + 1 = k by omega)] using this;
        . refine ⟨?_, ?_, ?_⟩;
          . suffices z ≠ x ∧ ∀ x ∈ S.Γ.fmls, ¬x.label = z by simpa;
            constructor;
            . assumption;
            . rintro ⟨w, ψ⟩ h rfl;
              have := not_include_labelledFml_of_isFreshLabel hΓz ψ;
              contradiction;
          . exact hΓz.2.1;
          . exact hΓz.2.2;
        . exact ih (by simp at kh; omega);

def wkFmlLₕ (d : ⊢ᵍ[k] Γ ⟹ Δ) : ⊢ᵍ[k] ⟨(x ∶ φ) ::ₘ Γ.fmls, Γ.rels⟩ ⟹ Δ := by
  obtain ⟨d, kh⟩ := d;
  cases d with
  | initAtom y a => exact initAtomₕ' y a (by simp) (by simp);
  | initBot y => exact initBotₕ' y (by simp);
  | _ => sorry;

def wkFmlL (d : ⊢ᵍ Γ ⟹ Δ) : ⊢ᵍ ⟨(x ∶ φ) ::ₘ Γ.fmls, Γ.rels⟩ ⟹ Δ := wkFmlLₕ (d := .ofDerivation d) |>.drv


def wkRelLₕ (d : ⊢ᵍ[h] Γ ⟹ Δ) : ⊢ᵍ[h] ⟨Γ.fmls, (x, y) ::ₘ Γ.rels⟩ ⟹ Δ := by sorry

def wkRelL (d : ⊢ᵍ Γ ⟹ Δ) : ⊢ᵍ ⟨Γ.fmls, (x, y) ::ₘ Γ.rels⟩ ⟹ Δ := wkRelLₕ (d := .ofDerivation d) |>.drv


def wkFmlRₕ (d : ⊢ᵍ[h] Γ ⟹ Δ) : ⊢ᵍ[h] Γ ⟹ ⟨(x ∶ φ) ::ₘ Δ.fmls, Δ.rels⟩ := by sorry

def wkFmlR (d : ⊢ᵍ Γ ⟹ Δ) : ⊢ᵍ Γ ⟹ ⟨(x ∶ φ) ::ₘ Δ.fmls, Δ.rels⟩ := wkFmlRₕ (d := .ofDerivation d) |>.drv


def wkRelRₕ (d : ⊢ᵍ[h] Γ ⟹ Δ) : ⊢ᵍ[h] Γ ⟹ ⟨Δ.fmls, (x, y) ::ₘ Δ.rels⟩ := by sorry

def wkRelR (d : ⊢ᵍ Γ ⟹ Δ) : ⊢ᵍ Γ ⟹ ⟨Δ.fmls, (x, y) ::ₘ Δ.rels⟩ := wkRelRₕ (d := .ofDerivation d) |>.drv

end LO.Modal.Labelled.Gentzen
