import LabelledSystem.Gentzen.Basic

namespace LO.Modal.Labelled.Gentzen

open SequentPart
open DerivationWithHeight

noncomputable def replaceLabelₕAux (d : ⊢ᵍ[k] S) (σ : Label → Label) : ⊢ᵍ[k] S⟦σ⟧ := by
  obtain ⟨d, kh⟩ := d;
  induction d generalizing k with
  | initAtom y a => exact initAtomₕ' (σ y) a (by simp) (by simp);
  | initBot y => exact initBotₕ' (σ y) (by simp);
  | @impL S x φ ψ d₁ d₂ ih₁ ih₂ =>
    by_cases k = 0;
    . simp at kh; omega;
    . suffices ⊢ᵍ[k]
        ⟨(σ x ∶ φ ➝ ψ) ::ₘ S.Γ.fmls.map (.labelReplace σ), S.Γ.rels.map (.labelReplace σ)⟩ ⟹
        ⟨S.Δ.fmls.map (.labelReplace σ), S.Δ.rels.map (.labelReplace σ)⟩
         by simpa;
      have := @impLₕ
        (Γ := ⟨S.Γ.fmls.map (.labelReplace σ), S.Γ.rels.map (.labelReplace σ)⟩)
        (Δ := ⟨S.Δ.fmls.map (.labelReplace σ), S.Δ.rels.map (.labelReplace σ)⟩)
        (x := (σ x)) (φ := φ) (ψ := ψ) (k₁ := (k - 1)) (k₂ := (k - 1)) ?_ ?_;
      rwa [(show max (k - 1) (k - 1) + 1 = k by omega)] at this;
      . simpa using @ih₁ (k - 1) (by simp at kh; omega);
      . simpa using @ih₂ (k - 1) (by simp at kh; omega);
  | @impR S x φ ψ d ih =>
    by_cases k = 0;
    . simp at kh; omega;
    . suffices ⊢ᵍ[k]
        ⟨S.Γ.fmls.map (.labelReplace σ), S.Γ.rels.map (.labelReplace σ)⟩ ⟹
        ⟨(σ x ∶ φ ➝ ψ) ::ₘ S.Δ.fmls.map (.labelReplace σ), S.Δ.rels.map (.labelReplace σ)⟩
         by simpa;
      have := @impRₕ
        (Γ := ⟨S.Γ.fmls.map (.labelReplace σ), S.Γ.rels.map (.labelReplace σ)⟩)
        (Δ := ⟨S.Δ.fmls.map (.labelReplace σ), S.Δ.rels.map (.labelReplace σ)⟩)
        (x := (σ x)) (φ := φ) (ψ := ψ) (h := (k - 1)) ?_;
      rwa [(show k - 1 + 1 = k by omega)] at this;
      . simpa using @ih (k - 1) (by simp at kh; omega);
  | @boxL S x y φ d ih =>
    by_cases k = 0;
    . simp at kh; omega;
    . suffices ⊢ᵍ[k]
        ⟨(σ x ∶ □φ) ::ₘ S.Γ.fmls.map (.labelReplace σ), (σ x, σ y) ::ₘ S.Γ.rels.map (.labelReplace σ)⟩ ⟹
        ⟨S.Δ.fmls.map (.labelReplace σ), S.Δ.rels.map (.labelReplace σ)⟩
         by simpa;
      have := @boxLₕ
        (Γ := ⟨S.Γ.fmls.map (.labelReplace σ), S.Γ.rels.map (.labelReplace σ)⟩)
        (Δ := ⟨S.Δ.fmls.map (.labelReplace σ), S.Δ.rels.map (.labelReplace σ)⟩)
        (x := (σ x)) (y := (σ y)) (φ := φ) (k := k - 1) ?_;
      rwa [(show k - 1 + 1 = k by omega)] at this;
      . simpa using @ih (k - 1) (by simp at kh; omega);
  | @boxR S x y φ hxy hΓ hΔ d ih =>
    by_cases k = 0;
    . simp at kh; omega;
    . suffices ⊢ᵍ[k]
        ⟨S.Γ.fmls.map (.labelReplace σ), S.Γ.rels.map (.labelReplace σ)⟩ ⟹
        ⟨(σ x ∶ □φ) ::ₘ S.Δ.fmls.map (.labelReplace σ), S.Δ.rels.map (.labelReplace σ)⟩
         by simpa;
      by_cases e : y = σ x;
      . subst e;
        have := @boxRₕ
            (Γ := ⟨S.Γ.fmls.map (.labelReplace σ), S.Γ.rels.map (.labelReplace σ)⟩)
            (Δ := ⟨S.Δ.fmls.map (.labelReplace σ), S.Δ.rels.map (.labelReplace σ)⟩)
            (x := σ x) (y := x) (φ := φ) (h := k - 1) ?_ ?_ ?_ ?_;
        rwa [(show k - 1 + 1 = k by omega)] at this;
        . sorry;
        . refine ⟨?_, ?_, ?_⟩;
          . sorry;
          . sorry;
          . sorry;
        . refine ⟨?_, ?_, ?_⟩;
          . simp;
            rintro ⟨z, ψ⟩ hψ;
            simp;
            sorry;
          . simp;
            rintro z w v h₁ h₂ rfl;
            have := (not_include_relTerm_of_isFreshLabel₁ hΔ) (σ w);
            sorry;
          . simp;
            rintro z w v h₁ h₂ rfl;
            sorry;
        . simp
          -- have := @ih Γ Δ (k - 1) (by simp at kh; omega);
          sorry;
          -- simpa using ih (k := k - 1) (by simp at kh; omega);
      . have := @boxRₕ
            (Γ := ⟨S.Γ.fmls.map (.labelReplace σ), S.Γ.rels.map (.labelReplace σ)⟩)
            (Δ := ⟨S.Δ.fmls.map (.labelReplace σ), S.Δ.rels.map (.labelReplace σ)⟩)
            (x := σ x) (y := σ y) (φ := φ) (h := k - 1) ?_ ?_ ?_ ?_;
        rwa [(show k - 1 + 1 = k by omega)] at this;
        . by_contra hC;
          sorry;
        . have ⟨hΓ₁, hΓ₂, hΓ₃⟩ := hΓ;
          sorry;
        . refine ⟨?_, ?_, ?_⟩;
          . have := not_include_labelledFml_of_isFreshLabel hΔ;
            simp;
            rintro ⟨z, ψ⟩ hψ;
            simp;
            sorry;
          . simp;
            rintro z w v h₁ h₂ rfl;
            have := (not_include_relTerm_of_isFreshLabel₁ hΔ) (σ w);
            sorry;
          . simp;
            rintro z w v h₁ h₂ h₃;
            have := (not_include_relTerm_of_isFreshLabel₂ hΔ) (σ w);
            sorry;
        . simpa using @ih (k := k - 1) (by simp at kh; omega);

noncomputable def replaceLabelₕ (d : ⊢ᵍ[h] Γ ⟹ Δ) (σ : LabelReplace) : ⊢ᵍ[h] Γ⟦σ⟧ ⟹ Δ⟦σ⟧ := by
  simpa using replaceLabelₕAux d σ;

noncomputable def replaceLabel (d : ⊢ᵍ Γ ⟹ Δ) (σ : LabelReplace) : ⊢ᵍ Γ⟦σ⟧ ⟹ Δ⟦σ⟧ :=
  replaceLabelₕ (.ofDerivation d) σ |>.drv

end LO.Modal.Labelled.Gentzen
