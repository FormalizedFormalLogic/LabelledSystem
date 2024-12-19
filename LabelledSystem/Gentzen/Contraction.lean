import LabelledSystem.Gentzen.Inverted

namespace LO.Modal.Labelled.Gentzen

variable {S : Sequent}

def contraFmlLₕ (d : ⊢ᵍ[h] (⟨(x ∶ φ) ::ₘ (x ∶ φ) ::ₘ S.Γ.fmls, S.Γ.rels⟩ ⟹ S.Δ))
  : ⊢ᵍ[h] (⟨(x ∶ φ) ::ₘ S.Γ.fmls, S.Γ.rels⟩ ⟹ S.Δ) := by
  sorry

def contraFmlRₕ (d : ⊢ᵍ[h] S.Γ ⟹ ⟨(x ∶ φ) ::ₘ (x ∶ φ) ::ₘ S.Δ.fmls, S.Δ.rels⟩)
  : ⊢ᵍ[h] S.Γ ⟹ ⟨(x ∶ φ) ::ₘ S.Δ.fmls, S.Δ.rels⟩ := by
  sorry

def contraRelLₕ (d : ⊢ᵍ[h] (⟨S.Γ.fmls, (x, y) ::ₘ (x, y) ::ₘ S.Γ.rels⟩ ⟹ S.Δ))
  : ⊢ᵍ[h] (⟨S.Γ.fmls, (x, y) ::ₘ S.Γ.rels⟩ ⟹ S.Δ) := by
  sorry

def contraRelRₕ (d : ⊢ᵍ[h] S.Γ ⟹ ⟨S.Δ.fmls, (x, y) ::ₘ (x, y) ::ₘ S.Δ.rels⟩)
  : ⊢ᵍ[h] S.Γ ⟹ ⟨S.Δ.fmls, (x, y) ::ₘ S.Δ.rels⟩ := by
  sorry

end LO.Modal.Labelled.Gentzen
