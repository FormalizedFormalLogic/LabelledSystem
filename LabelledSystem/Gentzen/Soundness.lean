import LabelledSystem.Gentzen.Basic

namespace LO.Modal.Labelled.Gentzen

theorem soundness {S : Sequent} : ⊢ᵍ S → ∀ (M : Kripke.Model), ∀ (f : Assignment M), S.Satisfies M f := by
  intro d;
  induction d with
  | initAtom =>
    rintro M f ⟨hΓ, hX⟩;
    simp_all;
  | initBot =>
    rintro M f ⟨hΓ, hX⟩;
    simp at hΓ;
  | @impL Γ Δ x φ ψ d₁ d₂ ih₁ ih₂ =>
    rintro M f ⟨hΓ, hX⟩;
    have ⟨hΓ₁, hΓ₂⟩ : f ⊧ (x ∶ φ ➝ ψ) ∧ ∀ a ∈ Γ.fmls, f ⊧ a := by simpa using hΓ;
    replace hX : ∀ x y, ⟨x, y⟩ ∈ Γ.rels → LabelTerm.evaluated f ⟨x, y⟩ := by simpa using hX;
    have : ¬(f x ⊧ φ) ∨ (f x ⊧ ψ) := by
      simpa [LabelledFormula.Satisfies.imp_def, Semantics.Imp.realize_imp, imp_iff_not_or] using hΓ₁;
    rcases this with (_ | h);
    . replace ih₁ :
        (∀ lφ ∈ Γ.fmls, f ⊧ lφ) →
        (∀ a b, (a, b) ∈ Γ.rels → LabelTerm.evaluated f (a, b)) →
        ((f x) ⊧ φ ∨ ∃ a ∈ Δ.fmls, f ⊧ a) ∨ ∃ a b, (a, b) ∈ Δ.rels ∧ LabelTerm.evaluated f (a, b)
        := by simpa [Sequent.Satisfies] using ih₁ M f;
      rcases ih₁ hΓ₂ hX with (_ | ⟨lψ, _, _⟩) | _;
      . simp_all;
      . left; use lψ;
      . simp_all;
    . replace ih₂ :
          (f x) ⊧ ψ →
          (∀ a ∈ Γ.fmls, f ⊧ a) →
          (∀ a b, (a, b) ∈ Γ.rels → LabelTerm.evaluated f (a, b)) →
          (∃ lφ ∈ Δ.fmls, f ⊧ lφ) ∨ ∃ a b, (a, b) ∈ Δ.rels ∧ LabelTerm.evaluated f (a, b)
          := by simpa [Sequent.Satisfies] using ih₂ M f;
      rcases ih₂ h hΓ₂ hX with _ | _ <;> simp_all;
  | @impR Γ Δ x φ ψ d ih =>
    rintro M f ⟨hΓ, hX⟩;
    suffices ((¬(f x) ⊧ φ ∨ (f x) ⊧ ψ) ∨ ∃ a ∈ Δ.fmls, f ⊧ a) ∨ ∃ a b, (a, b) ∈ Δ.rels ∧ LabelTerm.evaluated f (a, b) by
      simpa [LabelledFormula.Satisfies.imp_def, Semantics.Imp.realize_imp, imp_iff_not_or];
    wlog _ : (f x) ⊧ φ;
    . tauto;
    replace ih :
      (f ⊧ x ∶ φ) →
      (∀ a ∈ Γ.fmls, f ⊧ a) →
      (∀ a b, (a, b) ∈ Γ.rels → LabelTerm.evaluated f (a, b)) →
      ((f ⊧ x ∶ ψ) ∨ ∃ a ∈ Δ.fmls, f ⊧ a) ∨ ∃ a b, (a, b) ∈ Δ.rels ∧ LabelTerm.evaluated f (a, b)
      := by simpa [Sequent.Satisfies] using ih M f;
    rcases ih (by simpa) (by simpa using hΓ) (by simpa using hX) with (h | _) | _;
    . tauto;
    . simp_all;
    . simp_all;
  | @boxL Γ Δ x y φ d ih =>
    rintro M f ⟨hΓ, hX⟩;

    have ⟨hxbφ, hΓ₂⟩ : (f ⊧ x ∶ □φ) ∧ ∀ a ∈ Γ.fmls, f ⊧ a := by simpa using hΓ;
    have ⟨hxy, hX₂⟩ : LabelTerm.evaluated f (x, y) ∧ ∀ a b, (a, b) ∈ Γ.rels → LabelTerm.evaluated f (a, b) := by simpa using hX;
    have hyφ : f ⊧ y ∶ φ := Formula.Kripke.Satisfies.box_def.mp (LabelledFormula.Satisfies.box_def.mp hxbφ) _ hxy;

    replace ih :
      (f ⊧ x ∶ □φ) →
      (f ⊧ y ∶ φ) →
      (∀ a ∈ Γ.fmls, f ⊧ a) →
      LabelTerm.evaluated f (x, y) →
      (∀ a b, (a, b) ∈ Γ.rels → LabelTerm.evaluated f (a, b)) →
      (∃ lφ ∈ Δ.fmls, f ⊧ lφ) ∨ ∃ a b, (a, b) ∈ Δ.rels ∧ LabelTerm.evaluated f (a, b) := by simpa [Sequent.Satisfies] using ih M f;

    rcases ih hxbφ hyφ hΓ₂ hxy hX₂ with _ | _ <;> simp_all;
  | @boxR Γ Δ x y φ hxy hyΓ hyΔ d ih =>
    rintro M f ⟨hΓ, hX⟩;

    suffices ((f ⊧ x ∶ □φ) ∨ ∃ a ∈ Δ.fmls, f ⊧ a) ∨ ∃ a b, (a, b) ∈ Δ.rels ∧ LabelTerm.evaluated f (a, b) by simpa;
    apply or_iff_not_imp_right.mpr;
    intro hΔ₁; push_neg at hΔ₁;
    apply or_iff_not_imp_right.mpr;
    intro hΔ₂; push_neg at hΔ₂;

    intro w hw;
    let g : Assignment M := λ z => if z = y then w else f z;

    replace ih :
      (∀ lφ ∈ Γ.fmls, g ⊧ lφ) →
      LabelTerm.evaluated g (x, y) →
      (∀ a b, (a, b) ∈ Γ.rels → LabelTerm.evaluated g (a, b)) →
      ((g ⊧ y ∶ φ) ∨ ∃ a ∈ Δ.fmls, g ⊧ a) ∨ ∃ a b, (a, b) ∈ Δ.rels ∧ LabelTerm.evaluated g (a, b)
      := by simpa [Sequent.Satisfies] using ih M g;
    have : ∀ lφ ∈ Γ.fmls, g ⊧ lφ := by
      rintro ⟨a, ψ⟩ hz;
      have ha : a ≠ y := by
        rintro rfl;
        have := SequentPart.not_include_labelledFml_of_isFreshLabel hyΓ ψ;
        contradiction;
      simpa [g, ha] using hΓ _ hz
    have : LabelTerm.evaluated g (x, y) := by simpa [LabelTerm.evaluated, g, hxy];
    have : ∀ a b, (a, b) ∈ Γ.rels → LabelTerm.evaluated g (a, b) := (by
      intro a b r;
      have ha : a ≠ y := by
        rintro rfl;
        have := SequentPart.not_include_relTerm_of_isFreshLabel₁ hyΓ b;
        contradiction;
      have hb : b ≠ y := by
        rintro rfl;
        have := SequentPart.not_include_relTerm_of_isFreshLabel₂ hyΓ a;
        contradiction;
      simpa [LabelTerm.evaluated, g, ha, hb] using hX (a, b) r;
    )
    rcases ih (by assumption) (by assumption) (by assumption) with (h | ⟨⟨z, ψ⟩, h₁, h₂⟩) | ⟨a, b, h₁, h₂⟩;
    . simpa [g, LabelledFormula.Satisfies.iff_models] using h;
    . have hz : z ≠ y := by
        rintro rfl;
        have := SequentPart.not_include_labelledFml_of_isFreshLabel hyΔ ψ;
        contradiction;
      have :  f ⊧ z ∶ ψ := by simpa [g, hz] using h₂;
      have : ¬f ⊧ z ∶ ψ := hΔ₂ _ h₁;
      contradiction;
    . have ha : a ≠ y := by
        rintro rfl;
        have := SequentPart.not_include_relTerm_of_isFreshLabel₁ hyΔ b;
        contradiction;
      have hb : b ≠ y := by
        rintro rfl;
        have := SequentPart.not_include_relTerm_of_isFreshLabel₂ hyΔ a;
        contradiction;
      have :  (f a) ≺ (f b) := by simpa [LabelTerm.evaluated, g, ha, hb] using h₂;
      have : ¬(f a) ≺ (f b) := hΔ₁ a b h₁;
      contradiction;

theorem soundness_fml {φ : Formula ℕ} : ⊢ᵍ! ↑φ → ∀ (M : Kripke.Model), ∀ (f : Assignment M), f 0 ⊧ φ := by
  rintro ⟨d⟩ M f;
  simpa [Sequent.Satisfies] using soundness d M f

end LO.Modal.Labelled.Gentzen
