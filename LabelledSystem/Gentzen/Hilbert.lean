import LabelledSystem.Gentzen.Basic

namespace LO.Modal.Labelled.Gentzen

-- def Sequent.ofFormula (φ : Formula ℕ) : Sequent := ⟨∅, ∅⟩ ⟹ ⟨{0 ∶ φ}, ∅⟩

variable {x : Label} {φ ψ χ : Formula ℕ}

def imply₁ : ⊢ᵍ ⟨∅, ∅⟩ ⟹ ⟨{x ∶ φ ➝ ψ ➝ φ}, ∅⟩ := by
  apply impR (Δ := ⟨_, _⟩);
  apply impR (Δ := ⟨_, _⟩);
  have e : (x ∶ ψ) ::ₘ {x ∶ φ} = (x ∶ φ) ::ₘ {x ∶ ψ} := by sorry;
  exact initFml' x φ (by simp) (by simp);

def imply₂ : ⊢ᵍ ⟨∅, ∅⟩ ⟹ ⟨{x ∶ (φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ}, ∅⟩ := by
  apply impR (Δ := ⟨_, _⟩);
  apply impR (Δ := ⟨_, _⟩);
  apply impR (Δ := ⟨_, _⟩);
  rw [Multiset.cons_swap];
  apply impL (Γ := ⟨{x ∶ φ, x ∶ φ ➝ ψ ➝ χ}, _⟩);
  . exact initFml' x φ (by simp) (by simp);
  . suffices ⊢ᵍ ⟨(x ∶ φ ➝ ψ ➝ χ) ::ₘ {x ∶ ψ, x ∶ φ}, ∅⟩ ⟹ ⟨{x ∶ χ}, ∅⟩ by
      have e : (x ∶ ψ) ::ₘ (x ∶ φ) ::ₘ {x ∶ φ ➝ ψ ➝ χ} = (x ∶ φ ➝ ψ ➝ χ) ::ₘ {x ∶ ψ, x ∶ φ} := by sorry;
      simpa [e];
    apply impL (Γ := ⟨_, _⟩);
    . exact initFml' x φ (by simp) (by simp);
    . apply impL (Γ := ⟨_, _⟩);
      . exact initFml' x ψ (by simp) (by simp);
      . exact initFml' x χ (by simp) (by simp);

def elimContra : ⊢ᵍ ⟨∅, ∅⟩ ⟹ ⟨{x ∶ (∼ψ ➝ ∼φ) ➝ (φ ➝ ψ)}, ∅⟩ := by
  apply impR (Δ := ⟨_, _⟩);
  apply impR (Δ := ⟨_, _⟩);
  rw [Multiset.cons_swap];
  apply impL (Γ := ⟨{x ∶ φ}, _⟩);
  . -- TODO: `⊢ᵍ Γ ⟹ ⟨(x ∶ ∼ψ) ::ₘ {x ∶ ψ}, Δ.rels⟩`
    apply impR (Δ := ⟨_, _⟩);
    exact initFml' x ψ (by simp) (by simp);
  . -- TODO: `⊢ᵍ ⟨(x ∶ ∼φ) ::ₘ {x ∶ φ} :: Γ.fmls, ∅⟩ ⟹ Δ`
    apply impL (Γ := ⟨{x ∶ φ}, _⟩);
    . exact initFml' x φ (by simp) (by simp);
    . exact initBot;

def axiomK : ⊢ᵍ ⟨∅, ∅⟩ ⟹ ⟨{x ∶ □(φ ➝ ψ) ➝ □φ ➝ □ψ}, ∅⟩ := by
  letI y : Label := x + 1;
  apply impR (Δ := ⟨_, _⟩);
  apply impR;
  apply boxR (y := y) (by simp [y]) (by simp) (by simp);
  suffices ⊢ᵍ (⟨(x ∶ □φ) ::ₘ {x ∶ □(φ ➝ ψ)}, {(x, y)}⟩ ⟹ ⟨{y ∶ ψ}, ∅⟩) by simpa;
  apply boxL (Γ := ⟨_, _⟩);
  suffices ⊢ᵍ (⟨(x ∶ □(φ ➝ ψ)) ::ₘ (y ∶ φ) ::ₘ {(x ∶ □φ)}, {(x, y)}⟩ ⟹ ⟨{y ∶ ψ}, ∅⟩) by
    have e : (x ∶ □(φ ➝ ψ)) ::ₘ (y ∶ φ) ::ₘ {x ∶ □φ} = (x ∶ □φ) ::ₘ (y ∶ φ) ::ₘ {x ∶ □(φ ➝ ψ)} := by sorry;
    simpa [e];
  apply boxL (Γ := ⟨{y ∶ φ, x ∶ □φ}, _⟩);
  suffices ⊢ᵍ (⟨(y ∶ φ ➝ ψ) ::ₘ {y ∶ φ, x ∶ □φ, x ∶ □(φ ➝ ψ)}, {(x, y)}⟩ ⟹ ⟨{y ∶ ψ}, ∅⟩) by
    have e : (x ∶ □(φ ➝ ψ)) ::ₘ (y ∶ φ ➝ ψ) ::ₘ (y ∶ φ) ::ₘ {x ∶ □φ} = (y ∶ φ ➝ ψ) ::ₘ {y ∶ φ, x ∶ □φ, x ∶ □(φ ➝ ψ)} := by sorry;
    simpa [e];
  apply impL (Γ := ⟨_, _⟩);
  . exact initFml' y φ (by simp) (by simp);
  . exact initFml' y ψ (by simp) (by simp);

def mdp (d₁ : ⊢ᵍ ⟨∅, ∅⟩ ⟹ ⟨{x ∶ φ ➝ ψ}, ∅⟩) (d₂ : ⊢ᵍ ⟨∅, ∅⟩ ⟹ ⟨{x ∶ φ}, ∅⟩) : ⊢ᵍ ⟨∅, ∅⟩ ⟹ ⟨{x ∶ ψ}, ∅⟩ := by
  simpa using cutFml (Δ₁ := ⟨∅, ∅⟩) (Δ₂ := ⟨{x ∶ ψ}, ∅⟩) d₂ $ implyRInv (Δ := ⟨∅, ∅⟩) d₁;

def necessitation (d : ⊢ᵍ ⟨∅, ∅⟩ ⟹ ⟨{x ∶ φ}, ∅⟩) : ⊢ᵍ ⟨∅, ∅⟩ ⟹ ⟨{x ∶ □φ}, ∅⟩ := by
  letI y : Label := x + 1;
  apply boxR (Δ := ⟨∅, ∅⟩) (y := y) (by simp [y]) (by simp) (by simp);
  apply wkRelL;
  simpa [SequentPart.replaceLabel, LabelledFormula.labelReplace, LabelReplace.specific] using replaceLabel d (x ⧸ y);

end LO.Modal.Labelled.Gentzen
