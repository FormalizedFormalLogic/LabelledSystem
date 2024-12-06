import Foundation.Modal.NNFormula
import Foundation.Modal.Kripke.Basic

namespace LO.Modal


namespace Labelled


abbrev Label := ℕ

def Assignment (M : Kripke.Model) := Label → M.World


abbrev LabelReplace := Label → Label

namespace LabelReplace

abbrev specific (x : Label) (y : Label) : LabelReplace := λ z => if z = x then y else z
infixr:90 "⧸" => specific

end LabelReplace


abbrev LabelTerm := Label × Label

namespace LabelTerm

def evaluated {M : Kripke.Model} (f : Assignment M) : LabelTerm → Prop := λ ⟨x, y⟩ => (f x) ≺ (f y)

def replace (σ : LabelReplace) : LabelTerm → LabelTerm := λ (x, y) => ⟨σ x, σ y⟩

end LabelTerm


structure LabelledFormula where
  label : Label
  formula : Formula ℕ
deriving DecidableEq, Repr

namespace LabelledFormula

notation:95 x " ∶ " φ => LabelledFormula.mk x φ

def labelReplace (σ : Label → Label) : LabelledFormula → LabelledFormula := λ ⟨x, φ⟩ => ⟨σ x, φ⟩
notation lφ "⟦" σ "⟧" => labelReplace σ lφ


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
