import Foundation.Modal.NNFormula
import Foundation.Modal.Kripke.Basic

namespace LO.Modal


namespace Labelled


abbrev Label := ℕ

namespace Label

def Assignment (M : Kripke.Model) := Label → M.World

end Label


abbrev LabelTerm := Label × Label

namespace LabelTerm

def evaluated {M : Kripke.Model} (f : Label.Assignment M) : LabelTerm → Prop := λ ⟨x, y⟩ => M.Rel (f x) (f y)

end LabelTerm


structure LabelledFormula where
  label : Label
  formula : Formula ℕ
deriving DecidableEq, Repr

namespace LabelledFormula

notation:95 x " ∶ " φ => LabelledFormula.mk x φ

def Satisfies (M : Kripke.Model) (f : Label.Assignment M) : LabelledFormula → Prop := λ (x ∶ φ) => (f x) ⊧ φ

namespace Satisfies

protected instance semantics {M : Kripke.Model} : Semantics (LabelledFormula) (Label.Assignment M) := ⟨fun x ↦ LabelledFormula.Satisfies M x⟩


variable {M : Kripke.Model} {f : Label.Assignment M}
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
