import LabelledSystem.Gentzen.Cut
import LabelledSystem.Gentzen.Weakening
import LabelledSystem.Gentzen.Inverted

namespace LO.Modal

namespace Labelled.Gentzen

open SequentPart

variable {x : Label} {φ ψ χ : Formula PropVar}

def imply₁ : ⊢ᵍ ↑(φ ➝ ψ ➝ φ) := by
  apply impR₂ (Δ := ⟨_, _⟩);
  apply impR₂ (Δ := ⟨_, _⟩);
  have e : (0 ∶ ψ) ::ₘ {0 ∶ φ} = (0 ∶ φ) ::ₘ {0 ∶ ψ} := by apply Multiset.cons_swap;
  exact initFml' default φ (by simp) (by simp);

def imply₂ : ⊢ᵍ ↑((φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ) := by
  letI x : Label := default;
  apply impR₂ (Δ := ⟨_, _⟩);
  apply impR₂ (Δ := ⟨_, _⟩);
  apply impR₂ (Δ := ⟨_, _⟩);
  rw [Multiset.cons_swap];
  apply impL₂ (Γ := ⟨{0 ∶ φ, 0 ∶ φ ➝ ψ ➝ χ}, _⟩);
  . exact initFml₂' 0 φ (by simp) (by simp [x]);
  . suffices ⊢ᵍ ⟨(0 ∶ φ ➝ ψ ➝ χ) ::ₘ {0 ∶ ψ, 0 ∶ φ}, ∅⟩ ⟹ ⟨{0 ∶ χ}, ∅⟩ by
      have e : (0 ∶ ψ) ::ₘ (0 ∶ φ) ::ₘ {0 ∶ φ ➝ ψ ➝ χ} = (0 ∶ φ ➝ ψ ➝ χ) ::ₘ {0 ∶ ψ, 0 ∶ φ} := by
        ext;
        simp_rw [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton];
        omega;
      simpa [e];
    apply impL₂ (Γ := ⟨_, _⟩);
    . exact initFml' 0 φ (by simp) (by simp);
    . apply impL₂ (Γ := ⟨_, _⟩);
      . exact initFml' 0 ψ (by simp) (by simp);
      . exact initFml' 0 χ (by simp) (by simp);

def elimContra : ⊢ᵍ ↑((∼ψ ➝ ∼φ) ➝ (φ ➝ ψ)) := by
  apply impR₂ (Δ := ⟨_, _⟩);
  apply impR₂ (Δ := ⟨_, _⟩);
  rw [Multiset.cons_swap];
  apply impL₂ (Γ := ⟨{0 ∶ φ}, _⟩);
  . -- TODO: `⊢ᵍ Γ ⟹ ⟨(0 ∶ ∼ψ) ::ₘ {0 ∶ ψ}, Δ.rels⟩`
    apply impR₂ (Δ := ⟨_, _⟩);
    exact initFml' default ψ (by simp) (by simp);
  . -- TODO: `⊢ᵍ ⟨(0 ∶ ∼φ) ::ₘ {0 ∶ φ} :: Γ.fmls, ∅⟩ ⟹ Δ`
    apply impL₂ (Γ := ⟨{0 ∶ φ}, _⟩);
    . exact initFml' default φ (by simp) (by simp);
    . apply initBot' 0 (by tauto);

def axiomK : ⊢ᵍ ↑(□(φ ➝ ψ) ➝ □φ ➝ □ψ) := by
  apply impR₂ (Δ := ⟨_, _⟩);
  apply impR₂;
  apply boxR₂ (y := 1) (by simp) (by simp [isFreshLabel]) (by simp [isFreshLabel]);
  suffices ⊢ᵍ (⟨(0 ∶ □φ) ::ₘ {0 ∶ □(φ ➝ ψ)}, {(0, 1)}⟩ ⟹ ⟨{1 ∶ ψ}, ∅⟩) by simpa;
  apply boxL₂ (Γ := ⟨_, _⟩);
  suffices ⊢ᵍ (⟨(0 ∶ □(φ ➝ ψ)) ::ₘ (1 ∶ φ) ::ₘ {(0 ∶ □φ)}, {(0, 1)}⟩ ⟹ ⟨{1 ∶ ψ}, ∅⟩) by
    have e : (0 ∶ □(φ ➝ ψ)) ::ₘ (1 ∶ φ) ::ₘ {0 ∶ □φ} = (0 ∶ □φ) ::ₘ (1 ∶ φ) ::ₘ {0 ∶ □(φ ➝ ψ)} := by
      ext;
      simp_rw [Multiset.count_cons, Multiset.count_singleton];
      omega;
    simpa [e];
  apply boxL₂ (Γ := ⟨{1 ∶ φ, 0 ∶ □φ}, _⟩);
  suffices ⊢ᵍ (⟨(1 ∶ φ ➝ ψ) ::ₘ {1 ∶ φ, 0 ∶ □φ, 0 ∶ □(φ ➝ ψ)}, {(0, 1)}⟩ ⟹ ⟨{1 ∶ ψ}, ∅⟩) by
    have e : (0 ∶ □(φ ➝ ψ)) ::ₘ (1 ∶ φ ➝ ψ) ::ₘ (1 ∶ φ) ::ₘ {0 ∶ □φ} = (1 ∶ φ ➝ ψ) ::ₘ {1 ∶ φ, 0 ∶ □φ, 0 ∶ □(φ ➝ ψ)} := by
      ext;
      simp_rw [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton];
      omega;
    simpa [e];
  apply impL₂ (Γ := ⟨_, _⟩);
  . exact initFml' 1 φ (by simp) (by simp);
  . exact initFml' 1 ψ (by simp) (by simp);

def mdp (d₁ : ⊢ᵍ ↑(φ ➝ ψ)) (d₂ : ⊢ᵍ ↑φ) : ⊢ᵍ ↑ψ := by
  simpa using cutFml (Δ₁ := ⟨∅, ∅⟩) (Δ₂ := ⟨{_ ∶ ψ}, ∅⟩) d₂ $ implyRInv (Δ := ⟨∅, ∅⟩) d₁;

def necessitation (d : ⊢ᵍ ↑φ) : ⊢ᵍ ↑(□φ) := by
  apply boxR₂ (Δ := ⟨∅, ∅⟩) (y := 1) (by simp) (by simp [isFreshLabel]) (by simp [isFreshLabel]);
  apply wkRelL;
  simpa [SequentPart.replaceLabel, LabelledFormula.labelReplace, LabelReplace.specific] using replaceLabel d (0 ⧸ 1);


theorem ofHilbertK! (h : Hilbert.K ℕ ⊢! φ) : ⊢ᵍ! ↑φ := by
  induction h using Hilbert.Deduction.inducition_with_necOnly! with
  | hMdp ihφψ ihφ => exact ⟨mdp ihφψ.some ihφ.some⟩
  | hNec ihφ => exact ⟨necessitation ihφ.some⟩
  | hImply₁ => exact ⟨imply₁⟩
  | hImply₂ => exact ⟨imply₂⟩
  | hElimContra => exact ⟨elimContra⟩
  | hMaxm h =>
    rcases h with ⟨_, _, rfl⟩;
    . exact ⟨axiomK⟩;

end Labelled.Gentzen

end LO.Modal
