import LabelledSystem.Gentzen.Weakening
import LabelledSystem.Gentzen.Inverted
import LabelledSystem.Gentzen.Cut

namespace LO.Modal

namespace Labelled.Gentzen

open SequentPart

section

variable {Φ Ψ : Multiset LabelledFormula} {X Y : Multiset LabelTerm}

def impRₐ (x φ ψ) :
  (⊢ᵍ (⟨(x ∶ φ) ::ₘ Φ, X⟩ ⟹ ⟨(x ∶ ψ) ::ₘ Ψ, Y⟩)) →
  (⊢ᵍ (⟨Φ, X⟩ ⟹ ⟨(x ∶ φ ➝ ψ) ::ₘ Ψ, Y⟩))
  := impR (S := ⟨Φ, X⟩ ⟹ ⟨Ψ, Y⟩) x φ ψ

def impLₐ (x φ ψ) :
  ⊢ᵍ (⟨Φ, X⟩ ⟹ ⟨(x ∶ φ) ::ₘ Ψ, Y⟩) →
  ⊢ᵍ (⟨(x ∶ ψ) ::ₘ Φ, X⟩ ⟹ ⟨Ψ, Y⟩) →
  ⊢ᵍ (⟨(x ∶ φ ➝ ψ) ::ₘ Φ, X⟩ ⟹ ⟨Ψ, Y⟩)
  := impL (S := ⟨Φ, X⟩ ⟹ ⟨Ψ, Y⟩) x φ ψ

def boxLₐ (x y φ) :
  (⊢ᵍ (⟨(x ∶ □φ) ::ₘ (y ∶ φ) ::ₘ Φ, (x, y) ::ₘ X⟩ ⟹ ⟨Ψ, Y⟩)) →
  (⊢ᵍ (⟨(x ∶ □φ) ::ₘ Φ, (x, y) ::ₘ X⟩ ⟹ ⟨Ψ, Y⟩))
  := boxL (S := ⟨Φ, X⟩ ⟹ ⟨Ψ, Y⟩) x y φ

def boxRₐ (x y φ) : x ≠ y → isFreshLabel y (⟨Φ, X⟩) → isFreshLabel y (⟨Ψ, Y⟩) →
  ⊢ᵍ (⟨Φ, (x, y) ::ₘ X⟩ ⟹ ⟨(y ∶ φ) ::ₘ Ψ, Y⟩) →
  ⊢ᵍ (⟨Φ, X⟩ ⟹ ⟨(x ∶ □φ) ::ₘ Ψ, Y⟩)
  := boxR (S := ⟨Φ, X⟩ ⟹ ⟨Ψ, Y⟩) x y φ

noncomputable def wkFmlLₐ (x φ) :
  ⊢ᵍ (⟨Φ, X⟩ ⟹ ⟨Ψ, Y⟩) →
  ⊢ᵍ (⟨(x ∶ φ) ::ₘ Φ, X⟩ ⟹ ⟨Ψ, Y⟩)
  := wkFmlL

noncomputable def wkRelLₐ (x y) :
  ⊢ᵍ (⟨Φ, X⟩ ⟹ ⟨Ψ, Y⟩) →
  ⊢ᵍ (⟨Φ, (x, y) ::ₘ X⟩ ⟹ ⟨Ψ, Y⟩)
  := by sorry

noncomputable def replaceLabelₐ (x y : Label) :
  ⊢ᵍ (⟨Φ, X⟩ ⟹ ⟨Ψ, Y⟩) →
  ⊢ᵍ (⟨Φ⟦x ↦ y⟧, X⟦x ↦ y⟧⟩ ⟹ ⟨Ψ⟦x ↦ y⟧, Y⟦x ↦ y⟧⟩)
  := replaceLabel x y

end



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

def mdp (d₁ : ⊢ᵍ ↑(φ ➝ ψ)) (d₂ : ⊢ᵍ ↑φ) : ⊢ᵍ ↑ψ := by
  simpa using cutFml (Δ₁ := ⟨∅, ∅⟩) (Δ₂ := ⟨{_ ∶ ψ}, ∅⟩) d₂ $ implyRInv (Δ := ⟨∅, ∅⟩) d₁;

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
