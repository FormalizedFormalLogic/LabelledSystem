import LabelledSystem.Gentzen.Basic

namespace LO.Modal.Labelled.Gentzen

def cutRel (d₁ : ⊢ᵍ Γ₁ ⟹ ⟨Δ₁.fmls, (x, y) ::ₘ Δ₁.rels⟩) (d₂ : ⊢ᵍ ⟨Γ₂.fmls, (x, y) ::ₘ Γ₂.rels⟩ ⟹ Δ₂) : ⊢ᵍ (Γ₁ + Γ₂) ⟹ (Δ₁ + Δ₂) := by
  sorry

def cutFml (d₁ : ⊢ᵍ Γ₁ ⟹ ⟨(x ∶ φ) ::ₘ Δ₁.fmls, Δ₁.rels⟩) (d₂ : ⊢ᵍ ⟨(x ∶ φ) ::ₘ Γ₂.fmls, Γ₂.rels⟩ ⟹ Δ₂) : ⊢ᵍ (Γ₁ + Γ₂) ⟹ (Δ₁ + Δ₂) := by
  sorry

end LO.Modal.Labelled.Gentzen
