import LabelledSystem.Gentzen.Basic

namespace LO.Modal.Labelled.Gentzen

open Formula
open SequentPart
open DerivationWithHeight

noncomputable def replaceLabelₕAux' (x y) (d : ⊢ᵍ[k] S) : ⊢ᵍ[k] S⟦x ↦ y⟧ := by
  induction d using DerivationWithHeight.rec' with
  | hAtom z a k => exact initAtom_memₕ ((x ↦ y) z) a (by simp) (by simp);
  | hBot z => exact initBot_memₕ ((x ↦ y) z) (by simp);
  | @hImpR S z φ ψ k d ih =>
    suffices ⊢ᵍ[k + 1]
      ⟨S.Γ.fmls.map (.labelReplace _), S.Γ.rels.map (.labelReplace _)⟩ ⟹
      ⟨((x ↦ y) z ∶ φ ➝ ψ) ::ₘ S.Δ.fmls.map (.labelReplace _), S.Δ.rels.map (.labelReplace _)⟩
      by simpa;
    apply impRₕ
      (S := (⟨S.Γ.fmls.map (.labelReplace (x ↦ y)), S.Γ.rels.map (.labelReplace (x ↦ y))⟩ ⟹ ⟨S.Δ.fmls.map (.labelReplace (x ↦ y)), S.Δ.rels.map (.labelReplace (x ↦ y))⟩))
      ((x ↦ y) z) φ ψ ?_;
    . simpa using ih;
  | @hImpL S z φ ψ k₁ k₂ d₁ d₂ ih₁ ih₂ =>
    suffices ⊢ᵍ[(max k₁ k₂ + 1)]
      ⟨((x ↦ y) z ∶ φ ➝ ψ) ::ₘ S.Γ.fmls.map (.labelReplace (x ↦ y)), S.Γ.rels.map (.labelReplace (x ↦ y))⟩ ⟹
      ⟨S.Δ.fmls.map (.labelReplace (x ↦ y)), S.Δ.rels.map (.labelReplace (x ↦ y))⟩
      by simpa;
    apply impLₕ
      (S := (⟨S.Γ.fmls.map (.labelReplace (x ↦ y)), S.Γ.rels.map (.labelReplace (x ↦ y))⟩ ⟹ ⟨S.Δ.fmls.map (.labelReplace (x ↦ y)), S.Δ.rels.map (.labelReplace (x ↦ y))⟩))
      ((x ↦ y) z) φ ψ ?_ ?_;
    . simpa using ih₁;
    . simpa using ih₂;
  | @hBoxL S z w φ k d ih =>
    suffices ⊢ᵍ[k + 1]
      ⟨((x ↦ y) z ∶ □φ) ::ₘ S.Γ.fmls.map (.labelReplace (x ↦ y)), ((x ↦ y) z, (x ↦ y) w) ::ₘ S.Γ.rels.map (.labelReplace (x ↦ y))⟩ ⟹
      ⟨S.Δ.fmls.map (.labelReplace (x ↦ y)), S.Δ.rels.map (.labelReplace (x ↦ y))⟩
      by simpa;
    apply boxLₕ
      (S := (⟨S.Γ.fmls.map (.labelReplace (x ↦ y)), S.Γ.rels.map (.labelReplace (x ↦ y))⟩ ⟹ ⟨S.Δ.fmls.map (.labelReplace (x ↦ y)), S.Δ.rels.map (.labelReplace (x ↦ y))⟩))
      ((x ↦ y) z) ((x ↦ y) w) φ ?_;
    . simpa using ih;
  | @hBoxR S z w hyz hΓ hΔ φ k d ih =>
    suffices ⊢ᵍ[k + 1]
      ⟨S.Γ.fmls.map (.labelReplace (x ↦ y)), S.Γ.rels.map (.labelReplace (x ↦ y))⟩ ⟹
      ⟨((x ↦ y) z ∶ □φ) ::ₘ S.Δ.fmls.map (.labelReplace (x ↦ y)), S.Δ.rels.map (.labelReplace (x ↦ y))⟩
      by simpa;
    sorry;
    /-
    by_cases e : x = z;
    . subst e;
      apply @boxRₕ
        (S := (⟨S.Γ.fmls.map (.labelReplace (x ↦ y)), S.Γ.rels.map (.labelReplace (x ↦ y))⟩ ⟹ ⟨S.Δ.fmls.map (.labelReplace (x ↦ y)), S.Δ.rels.map (.labelReplace (x ↦ y))⟩))
        (x := y) (y := (x ↦ y) w) (k := k) φ ?_ ?_ ?_ ?_;
      . exact hyz.symm;
      . simp;
        sorry;
      . simp;
        sorry;
      . simp;
        sorry;
    . apply @boxRₕ
        (S := (⟨S.Γ.fmls.map (.labelReplace (x ↦ y)), S.Γ.rels.map (.labelReplace (x ↦ y))⟩ ⟹ ⟨S.Δ.fmls.map (.labelReplace (x ↦ y)), S.Δ.rels.map (.labelReplace (x ↦ y))⟩))
        (x := (x ↦ y) z) (y := (x ↦ y) w) (k := k) φ ?_ ?_ ?_ ?_;
      . simp;
        sorry;
      . apply SequentPart.of_isFreshLabel;
        . simp;
          sorry;
        . sorry;
        . sorry;
      . apply SequentPart.of_isFreshLabel;
        . sorry;
        . sorry;
        . sorry;
      . simpa using ih;
    -/

noncomputable def replaceLabelₕ (x y) (d : ⊢ᵍ[h] Γ ⟹ Δ) : ⊢ᵍ[h] Γ⟦x ↦ y⟧ ⟹ Δ⟦x ↦ y⟧ := by
  simpa using replaceLabelₕAux' x y d;

noncomputable def replaceLabel (x y) (d : ⊢ᵍ Γ ⟹ Δ) : ⊢ᵍ Γ⟦x ↦ y⟧ ⟹ Δ⟦x ↦ y⟧ :=
  replaceLabelₕ x y (.ofDerivation d) |>.drv

end LO.Modal.Labelled.Gentzen
