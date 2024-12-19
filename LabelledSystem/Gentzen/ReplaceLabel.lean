import LabelledSystem.Gentzen.Basic

namespace LO.Modal.Labelled.Gentzen

open Formula
open SequentPart
open DerivationWithHeight

noncomputable def replaceLabelₕ (x y) (d : ⊢ᵍ[k] S) : ⊢ᵍ[k] S⟦x ↦ y⟧ := by
  induction d using DerivationWithHeight.rec' generalizing x y with
  | hAtom z a k => exact initAtom_memₕ ((x ↦ y) z) a (by simp) (by simp);
  | hBot z => exact initBot_memₕ ((x ↦ y) z) (by simp);
  | @hImpR S z φ ψ k d ih =>
    suffices ⊢ᵍ[k + 1] ⟨S.Γ.fmls⟦_⟧, S.Γ.rels⟦_⟧⟩ ⟹ ⟨((x ↦ y) z ∶ φ ➝ ψ) ::ₘ S.Δ.fmls⟦_⟧, S.Δ.rels⟦_⟧⟩
      by simpa;
    apply impRₕ (S := (⟨S.Γ.fmls⟦_⟧, S.Γ.rels⟦_⟧⟩ ⟹ ⟨S.Δ.fmls⟦_⟧, S.Δ.rels⟦_⟧⟩))
      ((x ↦ y) z) φ ψ ?_;
    . simpa using ih x y;
  | @hImpL S z φ ψ k₁ k₂ d₁ d₂ ih₁ ih₂ =>
    suffices ⊢ᵍ[(max k₁ k₂ + 1)] ⟨((x ↦ y) z ∶ φ ➝ ψ) ::ₘ S.Γ.fmls⟦_⟧, S.Γ.rels⟦_⟧⟩ ⟹ ⟨S.Δ.fmls⟦_⟧, S.Δ.rels⟦_⟧⟩
      by simpa;
    apply impLₕ (S := (⟨S.Γ.fmls⟦_⟧, S.Γ.rels⟦_⟧⟩ ⟹ ⟨S.Δ.fmls⟦_⟧, S.Δ.rels⟦_⟧⟩))
      ((x ↦ y) z) φ ψ ?_ ?_;
    . simpa using ih₁ x y;
    . simpa using ih₂ x y;
  | @hBoxL S z w φ k d ih =>
    suffices ⊢ᵍ[k + 1] ⟨((x ↦ y) z ∶ □φ) ::ₘ S.Γ.fmls⟦_⟧, ((x ↦ y) z, (x ↦ y) w) ::ₘ S.Γ.rels⟦_⟧⟩ ⟹ ⟨S.Δ.fmls⟦_⟧, S.Δ.rels⟦_⟧⟩
      by simpa;
    apply boxLₕ (S := (⟨S.Γ.fmls⟦_⟧, S.Γ.rels⟦_⟧⟩ ⟹ ⟨S.Δ.fmls⟦_⟧, S.Δ.rels⟦_⟧⟩))
      ((x ↦ y) z) ((x ↦ y) w) φ ?_;
    . simpa using ih x y;
  | @hBoxR S z w hzw hΓw hΔw φ k d ih =>
    suffices ⊢ᵍ[k + 1] ⟨S.Γ.fmls⟦_⟧, S.Γ.rels⟦_⟧⟩ ⟹ ⟨((x ↦ y) z ∶ □φ) ::ₘ S.Δ.fmls⟦_⟧, S.Δ.rels⟦_⟧⟩ by simpa;
    by_cases ezx : x = z <;>
    by_cases ewx : x = w;
    . subst ezx ewx; contradiction;
    . subst ezx; clear ewx;
      have := ih x y;
      simp at this;
      have hw : (x ↦ y) w = w := LabelReplace.specific_ne (z := y) $ by tauto;
      let v := (S.Γ⟦x ↦ y⟧ ⟹ S.Δ⟦x ↦ y⟧).getFreshLabel;
      refine @boxRₕ (S := (S.Γ⟦x ↦ y⟧ ⟹ S.Δ⟦x ↦ y⟧)) k ((x ↦ y) x) v φ ?_ ?_ ?_ ?_;
      . simp;
        sorry;
      . sorry;
      . sorry;
      . sorry;
        -- simpa [hw] using ih x y;
    . subst ewx; clear ezx;
      have hz : (x ↦ y) z = z := LabelReplace.specific_ne (z := y) $ by tauto;
      let v := (S.Γ⟦x ↦ y⟧ ⟹ ⟨S.Δ.fmls⟦x ↦ y⟧, S.Δ.rels⟦x ↦ y⟧⟩).getFreshLabel;
      refine @boxRₕ (S := (S.Γ⟦x ↦ y⟧ ⟹ S.Δ⟦x ↦ y⟧)) k ((x ↦ y) z) v φ ?_ ?_ ?_ ?_;
      . simp [hz];
        sorry;
      . sorry;
      . sorry;
      . simp [hz];
        have := ih x v;
        simp at this;
        sorry;
    . have hz : (x ↦ y) z = z := LabelReplace.specific_ne (z := y) $ by tauto;
      have hw : (x ↦ y) w = w := LabelReplace.specific_ne (z := y) $ by tauto;
      refine @boxRₕ (S := (S.Γ⟦x ↦ y⟧ ⟹ S.Δ⟦x ↦ y⟧)) k ((x ↦ y) z) ((x ↦ y) w) φ ?_ ?_ ?_ ?_;
      . simpa [hz, hw];
      . sorry;
      . sorry;
      . simpa using ih _ _;

noncomputable def replaceLabel (x y) (d : ⊢ᵍ S) : ⊢ᵍ S⟦x ↦ y⟧ := replaceLabelₕ x y (.ofDerivation d) |>.drv

noncomputable def replaceLabelₐ (x y) :
  ⊢ᵍ (⟨Φ, X⟩ ⟹ ⟨Ψ, Y⟩) →
  ⊢ᵍ (⟨Φ⟦x ↦ y⟧, X⟦x ↦ y⟧⟩ ⟹ ⟨Ψ⟦x ↦ y⟧, Y⟦x ↦ y⟧⟩)
  := replaceLabel x y

end LO.Modal.Labelled.Gentzen
