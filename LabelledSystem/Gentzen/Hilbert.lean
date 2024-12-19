import LabelledSystem.Gentzen.Cut

namespace LO.Modal

namespace Labelled.Gentzen

open SequentPart

variable {x : Label} {φ ψ χ : Formula PropVar}

def imply₁ : ⊢ᵍ ↑(φ ➝ ψ ➝ φ) := by
  apply impRₐ;
  apply impRₐ;
  exact initFml_mem 0 φ (by simp) (by simp);

def imply₂ : ⊢ᵍ ↑((φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ) := by
  apply impRₐ;
  apply impRₐ;
  apply impRₐ;
  apply exchangeFmlL;
  apply impLₐ;
  . exact initFml_mem 0 φ (by simp) (by simp);
  . apply exchangeFml₃L;
    apply impLₐ;
    . exact initFml_mem 0 φ (by simp) (by simp);
    . apply impLₐ;
      . exact initFml_mem 0 ψ (by simp) (by simp);
      . exact initFml_mem 0 χ (by simp) (by simp);

def elimContra : ⊢ᵍ ↑((∼ψ ➝ ∼φ) ➝ (φ ➝ ψ)) := by
  apply impRₐ;
  apply impRₐ;
  apply exchangeFmlL;
  apply impLₐ;
  . apply impRₐ;
    exact initFml_mem 0 ψ (by simp) (by simp);
  . apply impLₐ;
    . exact initFml_mem 0 φ (by simp) (by simp);
    . exact initBot_mem 0 (by tauto);

def axiomK : ⊢ᵍ ↑(□(φ ➝ ψ) ➝ □φ ➝ □ψ) := by
  apply impRₐ;
  apply impRₐ;
  apply boxRₐ 0 1 ψ (by simp) (by simp [isFreshLabel]) (by simp [isFreshLabel]);
  apply boxLₐ;
  apply exchangeFml₃L;
  apply boxLₐ;
  apply exchangeFmlL;
  apply impLₐ;
  . exact initFml_mem 1 φ (by simp) (by simp);
  . exact initFml_mem 1 ψ (by simp) (by simp);

noncomputable def mdp (d₁ : ⊢ᵍ ↑(φ ➝ ψ)) (d₂ : ⊢ᵍ ↑φ) : ⊢ᵍ ↑ψ := cutFmlₐ 0 φ d₂ (implyRInvₐ d₁)

noncomputable def necessitation (d : ⊢ᵍ ↑φ) : ⊢ᵍ ↑(□φ) := by
  apply boxRₐ 0 1 φ (by simp) (by simp [isFreshLabel]) (by simp [isFreshLabel]);
  apply wkRelLₐ 0 1;
  exact replaceLabelₐ 0 1 d;

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
