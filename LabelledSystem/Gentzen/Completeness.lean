import LabelledSystem.Gentzen.Hilbert
import LabelledSystem.Gentzen.Soundness
import Foundation.Modal.Kripke.Completeness

namespace LO.Modal.Labelled.Gentzen

lemma completeness (h : ∀ (M : Kripke.Model), M ⊧ φ) : ⊢ᵍ! ↑φ := by
  apply ofHilbertK!;
  apply Hilbert.K.Kripke.complete |>.complete;
  intro F hF V x;
  exact h ⟨F, V⟩ x;

end LO.Modal.Labelled.Gentzen
