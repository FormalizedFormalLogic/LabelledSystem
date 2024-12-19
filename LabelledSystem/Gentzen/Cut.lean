import LabelledSystem.Gentzen.Contraction

namespace LO.Modal.Labelled.Gentzen

variable {S₁ S₂ : Sequent}
variable {Φ₁ Φ₂ Ψ₁ Ψ₂ : LabelledFormulae} {X₁ X₂ Y₁ Y₂ : RelTerms}

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

noncomputable def cutFmlₐ (x φ)
  (d₁ : ⊢ᵍ ⟨Φ₁, X₁⟩ ⟹ ⟨(x ∶ φ) ::ₘ Ψ₁, Y₁⟩)
  (d₂ : ⊢ᵍ ⟨(x ∶ φ) ::ₘ Φ₂, X₂⟩ ⟹ ⟨Ψ₂, Y₂⟩)
  : ⊢ᵍ (⟨Φ₁ + Φ₂, X₁ + X₂⟩) ⟹ (⟨Ψ₁ + Ψ₂, Y₁ + Y₂⟩) := by
  refine @cutFml (S₁ := ⟨Φ₁, X₁⟩ ⟹ ⟨Ψ₁, Y₁⟩) (S₂ := ⟨Φ₂, X₂⟩ ⟹ ⟨Ψ₂, Y₂⟩) x φ d₁ d₂;

end LO.Modal.Labelled.Gentzen
