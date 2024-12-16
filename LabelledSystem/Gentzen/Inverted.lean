import LabelledSystem.Gentzen.Basic

namespace LO.Modal.Labelled.Gentzen

variable {Γ Δ : SequentPart}

def implyRInvₕ (d : ⊢ᵍ[h] (Γ ⟹ ⟨(x ∶ φ ➝ ψ) ::ₘ Δ.fmls, Δ.rels⟩)) : ⊢ᵍ[h] (⟨(x ∶ φ) ::ₘ Γ.fmls, Γ.rels⟩ ⟹ ⟨(x ∶ ψ) ::ₘ Δ.fmls, Δ.rels⟩) := by sorry

def implyRInv (d : ⊢ᵍ (Γ ⟹ ⟨(x ∶ φ ➝ ψ) ::ₘ Δ.fmls, Δ.rels⟩)) : ⊢ᵍ (⟨(x ∶ φ) ::ₘ Γ.fmls, Γ.rels⟩ ⟹ ⟨(x ∶ ψ) ::ₘ Δ.fmls, Δ.rels⟩) := implyRInvₕ (d := .ofDerivation d) |>.drv

end LO.Modal.Labelled.Gentzen
