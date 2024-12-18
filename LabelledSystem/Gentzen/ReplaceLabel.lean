import LabelledSystem.Gentzen.Basic

namespace LO.Modal.Labelled.Gentzen

open Formula
open SequentPart
open DerivationWithHeight

noncomputable def replaceLabelₕ (x y) (d : ⊢ᵍ[k] S) : ⊢ᵍ[k] S⟦x ↦ y⟧ := by
  induction d using DerivationWithHeight.rec' with
  | hAtom z a k => exact initAtom_memₕ ((x ↦ y) z) a (by simp) (by simp);
  | hBot z => exact initBot_memₕ ((x ↦ y) z) (by simp);
  | @hImpR S z φ ψ k d ih =>
    suffices ⊢ᵍ[k + 1]
      ⟨S.Γ.fmls⟦_⟧, S.Γ.rels⟦_⟧⟩ ⟹
      ⟨((x ↦ y) z ∶ φ ➝ ψ) ::ₘ S.Δ.fmls⟦_⟧, S.Δ.rels⟦_⟧⟩
      by simpa;
    apply impRₕ
      (S := (⟨S.Γ.fmls⟦x ↦ y⟧, S.Γ.rels⟦x ↦ y⟧⟩ ⟹ ⟨S.Δ.fmls⟦x ↦ y⟧, S.Δ.rels⟦x ↦ y⟧⟩))
      ((x ↦ y) z) φ ψ ?_;
    . simpa using ih;
  | @hImpL S z φ ψ k₁ k₂ d₁ d₂ ih₁ ih₂ =>
    suffices ⊢ᵍ[(max k₁ k₂ + 1)]
      ⟨((x ↦ y) z ∶ φ ➝ ψ) ::ₘ S.Γ.fmls⟦x ↦ y⟧, S.Γ.rels⟦x ↦ y⟧⟩ ⟹
      ⟨S.Δ.fmls⟦x ↦ y⟧, S.Δ.rels⟦x ↦ y⟧⟩
      by simpa;
    apply impLₕ
      (S := (⟨S.Γ.fmls⟦x ↦ y⟧, S.Γ.rels⟦x ↦ y⟧⟩ ⟹ ⟨S.Δ.fmls⟦x ↦ y⟧, S.Δ.rels⟦x ↦ y⟧⟩))
      ((x ↦ y) z) φ ψ ?_ ?_;
    . simpa using ih₁;
    . simpa using ih₂;
  | @hBoxL S z w φ k d ih =>
    suffices ⊢ᵍ[k + 1]
      ⟨((x ↦ y) z ∶ □φ) ::ₘ S.Γ.fmls⟦x ↦ y⟧, ((x ↦ y) z, (x ↦ y) w) ::ₘ S.Γ.rels⟦x ↦ y⟧⟩ ⟹
      ⟨S.Δ.fmls⟦x ↦ y⟧, S.Δ.rels⟦x ↦ y⟧⟩
      by simpa;
    apply boxLₕ
      (S := (⟨S.Γ.fmls⟦x ↦ y⟧, S.Γ.rels⟦x ↦ y⟧⟩ ⟹ ⟨S.Δ.fmls⟦x ↦ y⟧, S.Δ.rels⟦x ↦ y⟧⟩))
      ((x ↦ y) z) ((x ↦ y) w) φ ?_;
    . simpa using ih;
  | @hBoxR S z w hyz hΓ hΔ φ k d ih =>
    suffices ⊢ᵍ[k + 1]
      ⟨S.Γ.fmls⟦x ↦ y⟧, S.Γ.rels⟦x ↦ y⟧⟩ ⟹
      ⟨((x ↦ y) z ∶ □φ) ::ₘ S.Δ.fmls⟦x ↦ y⟧, S.Δ.rels⟦x ↦ y⟧⟩
      by simpa;
    sorry;

noncomputable def replaceLabel (x y) (d : ⊢ᵍ S) : ⊢ᵍ S⟦x ↦ y⟧ := replaceLabelₕ x y (.ofDerivation d) |>.drv

noncomputable def replaceLabelₐ (x y) :
  ⊢ᵍ (⟨Φ, X⟩ ⟹ ⟨Ψ, Y⟩) →
  ⊢ᵍ (⟨Φ⟦x ↦ y⟧, X⟦x ↦ y⟧⟩ ⟹ ⟨Ψ⟦x ↦ y⟧, Y⟦x ↦ y⟧⟩)
  := replaceLabel x y

end LO.Modal.Labelled.Gentzen
