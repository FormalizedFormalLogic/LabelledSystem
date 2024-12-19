import LabelledSystem.Gentzen.Weakening

namespace LO.Modal.Labelled.Gentzen

variable {S : Sequent}

def implyRInvₕ
  (d : ⊢ᵍ[h] (S.Γ ⟹ ⟨(x ∶ φ ➝ ψ) ::ₘ S.Δ.fmls, S.Δ.rels⟩))
  : ⊢ᵍ[h] (⟨(x ∶ φ) ::ₘ S.Γ.fmls, S.Γ.rels⟩ ⟹ ⟨(x ∶ ψ) ::ₘ S.Δ.fmls, S.Δ.rels⟩) := by
  sorry;

def implyRInv
  (d : ⊢ᵍ (S.Γ ⟹ ⟨(x ∶ φ ➝ ψ) ::ₘ S.Δ.fmls, S.Δ.rels⟩))
  : ⊢ᵍ (⟨(x ∶ φ) ::ₘ S.Γ.fmls, S.Γ.rels⟩ ⟹ ⟨(x ∶ ψ) ::ₘ S.Δ.fmls, S.Δ.rels⟩)
  := implyRInvₕ (d := .ofDerivation d) |>.drv


def implyLInv₁ₕ
  (d : ⊢ᵍ[h] (⟨(x ∶ φ ➝ ψ) ::ₘ S.Γ.fmls, S.Γ.rels⟩ ⟹ S.Δ))
  : ⊢ᵍ[h] (S.Γ ⟹ ⟨(x ∶ φ) ::ₘ S.Δ.fmls, S.Δ.rels⟩) := by
  sorry

def implyLInv₁
  (d : ⊢ᵍ (⟨(x ∶ φ ➝ ψ) ::ₘ S.Γ.fmls, S.Γ.rels⟩ ⟹ S.Δ))
  : ⊢ᵍ (S.Γ ⟹ ⟨(x ∶ φ) ::ₘ S.Δ.fmls, S.Δ.rels⟩)
  := implyLInv₁ₕ (d := .ofDerivation d) |>.drv


def implyLInv₂ₕ
  (d : ⊢ᵍ[h] (⟨(x ∶ φ ➝ ψ) ::ₘ S.Γ.fmls, S.Γ.rels⟩ ⟹ S.Δ))
  : ⊢ᵍ[h] (⟨(x ∶ ψ) ::ₘ S.Γ.fmls, S.Γ.rels⟩ ⟹ S.Δ) := by
  sorry

def implyLInv₂
  (d : ⊢ᵍ (⟨(x ∶ φ ➝ ψ) ::ₘ S.Γ.fmls, S.Γ.rels⟩ ⟹ S.Δ))
  : ⊢ᵍ (⟨(x ∶ ψ) ::ₘ S.Γ.fmls, S.Γ.rels⟩ ⟹ S.Δ)
  := implyLInv₂ₕ (d := .ofDerivation d) |>.drv


noncomputable def boxLInvₕ
  (d : ⊢ᵍ[h] (⟨(x ∶ □φ) ::ₘ S.Γ.fmls, ((x, y) ::ₘ S.Γ.rels)⟩ ⟹ S.Δ))
  : ⊢ᵍ[h] (⟨(x ∶ □φ) ::ₘ (x ∶ φ) ::ₘ S.Γ.fmls, ((x, y) ::ₘ S.Γ.rels)⟩ ⟹ S.Δ)
  := exchangeFmlLₕ $ wkFmlLₕ (S := ⟨(x ∶ □φ) ::ₘ S.Γ.fmls, ((x, y) ::ₘ S.Γ.rels)⟩ ⟹ S.Δ) (k := h) (x := x) (φ := φ) d

noncomputable def boxRInvₕ
  (d : ⊢ᵍ[h] (S.Γ ⟹ ⟨(x ∶ □φ) ::ₘ S.Δ.fmls, S.Δ.rels⟩))
  (y) (hxy : x ≠ y) (hΓy : S.Γ.isFreshLabel y) (hΔy : S.Δ.isFreshLabel y)
  : ⊢ᵍ[h] (⟨S.Γ.fmls, (x, y) ::ₘ S.Γ.rels⟩ ⟹ ⟨(y ∶ φ) ::ₘ S.Δ.fmls, S.Δ.rels⟩)
  := by sorry

end LO.Modal.Labelled.Gentzen
