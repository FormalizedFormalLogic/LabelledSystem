import Foundation.Modal.NNFormula
import Foundation.Modal.Kripke.Basic

namespace LO.Modal


namespace Labelled


abbrev Label := ℕ

def Assignment (M : Kripke.Model) := Label → M.World


abbrev LabelReplace := Label → Label

namespace LabelReplace

variable {x y z : Label}

abbrev specific (x y : Label) : LabelReplace := λ z => if z = x then y else z
infixr:90 " ↦ " => specific

@[simp]
lemma specific_eq : (x ↦ y) x = y := by simp

lemma specific_ne (h : x ≠ y) : (x ↦ z) y = y := by
  simp [h];
  tauto;

end LabelReplace


abbrev LabelTerm := Label × Label

namespace LabelTerm

def evaluated {M : Kripke.Model} (f : Assignment M) : LabelTerm → Prop := λ ⟨x, y⟩ => (f x) ≺ (f y)


def labelReplace (σ : LabelReplace) : LabelTerm → LabelTerm := λ (x, y) => ⟨σ x, σ y⟩
notation R "⟦" σ "⟧" => labelReplace σ R

section

variable {x y z w: Label} {σ : LabelReplace}

@[simp] lemma def_labelReplace : (x, y)⟦σ⟧ = (σ x, σ y) := by rfl

@[simp] lemma labelReplace_specific₁ : (x, y)⟦x ↦ z⟧ = (z, (x ↦ z) y) := by simp;

@[simp] lemma labelReplace_specific₂ : (x, y)⟦y ↦ z⟧ = ((y ↦ z) x, z) := by simp;

lemma labelReplace_specific_not₁ (h : x ≠ z) : (x, y)⟦z ↦ w⟧ = (x, (z ↦ w) y) := by
  simp [def_labelReplace];
  tauto;

lemma labelReplace_specific_not₂ (h : y ≠ z) : (x, y)⟦z ↦ w⟧ = ((z ↦ w) x, y) := by
  simp [def_labelReplace];
  tauto;

lemma labelReplace_specific_not_both (h₁ : x ≠ z) (h₂ : y ≠ z) : (x, y)⟦z ↦ w⟧ = (x, y) := by
  simp [def_labelReplace];
  tauto;

end

end LabelTerm


structure LabelledFormula where
  label : Label
  formula : Formula ℕ
deriving DecidableEq, Repr

namespace LabelledFormula

notation:95 x " ∶ " φ => LabelledFormula.mk x φ


def labelReplace (σ : LabelReplace) : LabelledFormula → LabelledFormula := λ ⟨x, φ⟩ => ⟨σ x, φ⟩
notation lφ "⟦" σ "⟧" => labelReplace σ lφ

section

variable {x y z : Label} {φ ψ : Formula ℕ} {σ : LabelReplace}

@[simp]
lemma def_labelReplace : (x ∶ φ).labelReplace σ = (σ x ∶ φ) := by rfl

@[simp]
lemma labelReplace_specific : (x ∶ φ)⟦x ↦ y⟧ = (y ∶ φ) := by simp;

lemma labelReplace_specific_not (h : x ≠ y) : (x ∶ φ)⟦y ↦ z⟧ = (x ∶ φ) := by
  simp [def_labelReplace];
  tauto;

end


def Satisfies (M : Kripke.Model) (f : Assignment M) : LabelledFormula → Prop := λ (x ∶ φ) => (f x) ⊧ φ

namespace Satisfies

protected instance semantics {M : Kripke.Model} : Semantics (LabelledFormula) (Assignment M) := ⟨fun x ↦ LabelledFormula.Satisfies M x⟩

variable {M : Kripke.Model} {f : Assignment M}
variable {x y : Label}
variable {φ ψ : Formula ℕ} {xφ: LabelledFormula}

@[simp] protected lemma iff_models : f ⊧ (x ∶ φ) ↔ f x ⊧ φ := by tauto;

lemma imp_def : f ⊧ (x ∶ φ ➝ ψ) ↔ (f x) ⊧ φ ➝ ψ := by tauto;

lemma box_def : f ⊧ (x ∶ □φ) ↔ (f x) ⊧ □φ := by tauto;

end Satisfies

end LabelledFormula


structure LabelledNNFormula where
  label : Label
  formula : NNFormula ℕ
deriving DecidableEq, Repr

end Labelled

end LO.Modal
