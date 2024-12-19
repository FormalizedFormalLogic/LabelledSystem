import LabelledSystem.Gentzen.Contraction

namespace LO.Modal.Labelled.Gentzen

variable {S₁ S₂ : Sequent}

noncomputable def cutRel
  (d₁ : ⊢ᵍ S₁.Γ ⟹ ⟨S₁.Δ.fmls, (x, y) ::ₘ S₁.Δ.rels⟩)
  (d₂ : ⊢ᵍ ⟨S₂.Γ.fmls, (x, y) ::ₘ S₂.Γ.rels⟩ ⟹ S₂.Δ)
  : ⊢ᵍ (S₁.Γ + S₂.Γ) ⟹ (S₁.Δ + S₂.Δ) := by
  sorry

noncomputable def cutFml
  (d₁ : ⊢ᵍ S₁.Γ ⟹ ⟨(x ∶ φ) ::ₘ S₁.Δ.fmls, S₁.Δ.rels⟩)
  (d₂ : ⊢ᵍ ⟨(x ∶ φ) ::ₘ S₂.Γ.fmls, S₂.Γ.rels⟩ ⟹ S₂.Δ)
  : ⊢ᵍ (S₁.Γ + S₂.Γ) ⟹ (S₁.Δ + S₂.Δ) := by
  let c := φ.complexity
  induction c with
  | _ => sorry;

end LO.Modal.Labelled.Gentzen
