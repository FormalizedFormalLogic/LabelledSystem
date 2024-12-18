import LabelledSystem.Gentzen.ReplaceLabel

lemma Multiset.map_id_domain {s : Multiset α} (hf : ∀ a ∈ s, f a = a) : s.map f = s := by
  rw [Multiset.map_congr rfl hf];
  exact Multiset.map_id' s

namespace LO.Modal.Labelled.Gentzen

open SequentPart
open DerivationWithHeight

noncomputable def wkFmlLₕ (d : ⊢ᵍ[k] S) : ⊢ᵍ[k] ⟨(x ∶ φ) ::ₘ S.Γ.fmls, S.Γ.rels⟩ ⟹ S.Δ := by
  induction d using DerivationWithHeight.rec' generalizing x with
  | hAtom y a => exact initAtom_memₕ y a (by simp) (by simp);
  | hBot y => exact initBot_memₕ y (by simp);
  | @hImpR S y ψ χ k d ih =>
    suffices ⊢ᵍ[k + 1]
      ⟨(x ∶ φ) ::ₘ S.Γ.fmls, S.Γ.rels⟩ ⟹ ⟨(y ∶ ψ ➝ χ) ::ₘ S.Δ.fmls, S.Δ.rels⟩
      by simpa;
    refine impRₕ
      (S := ⟨(x ∶ φ) ::ₘ S.Γ.fmls, S.Γ.rels⟩ ⟹ S.Δ)
      (x := y) (φ := ψ) (ψ := χ) $ ?_;
    . exact exchangeFmlLₕ $ ih;
  | @hImpL S y ψ ξ k₁ k₂ d₁ d₂ ih₁ ih₂ =>
    suffices ⊢ᵍ[max k₁ k₂ + 1]
      ⟨(x ∶ φ) ::ₘ (y ∶ ψ ➝ ξ) ::ₘ S.Γ.fmls, S.Γ.rels⟩ ⟹ S.Δ
      by simpa;
    refine exchangeFmlLₕ $ impLₕ
      (S := ⟨(x ∶ φ) ::ₘ S.Γ.fmls, S.Γ.rels⟩ ⟹ S.Δ)
      (x := y) (φ := ψ) (ψ := ξ) ?_ ?_;
    . exact ih₁;
    . exact exchangeFmlLₕ $ ih₂;
  | @hBoxL S y z ψ k d ih =>
    suffices ⊢ᵍ[k + 1]
      ⟨(x ∶ φ) ::ₘ (y ∶ □ψ) ::ₘ S.Γ.fmls, (y, z) ::ₘ S.Γ.rels⟩ ⟹ S.Δ
      by simpa;
    refine exchangeFmlLₕ $ @boxLₕ
      (S := ⟨(x ∶ φ) ::ₘ S.Γ.fmls, S.Γ.rels⟩ ⟹ S.Δ)
      (x := y) (y := z) (φ := ψ) (k := k) ?_;
    . exact exchangeFml₃Lₕ $ ih;
  | @hBoxR S y z hyz hΓz hΔz ψ k d ih =>
    suffices ⊢ᵍ[k + 1]
      ⟨(x ∶ φ) ::ₘ S.Γ.fmls, S.Γ.rels⟩ ⟹ ⟨(y ∶ □ψ) ::ₘ S.Δ.fmls, S.Δ.rels⟩
      by simpa;
    by_cases e : z = x;
    . subst e;
      let w : Label := ((⟨(z ∶ φ) ::ₘ S.Γ.fmls, (y, z) ::ₘ S.Γ.rels⟩) ⟹ S.Δ).getFreshLabel;
      have := boxRₕ
        (S := ⟨(w ∶ φ) ::ₘ S.Γ.fmls, S.Γ.rels⟩ ⟹ S.Δ)
        (k := k) y z ψ hyz ?_ hΔz $ by simpa using @ih w;
      have := @replaceLabelₕ
        (x := w) (y := z) (k := k + 1)
        (S := { fmls := (w ∶ φ) ::ₘ S.Γ.fmls, rels := S.Γ.rels } ⟹ { fmls := (y ∶ □ψ) ::ₘ S.Δ.fmls, rels := S.Δ.rels })
        this;
      have e₁ : S.Γ.fmls⟦w ↦ z⟧ = S.Γ.fmls := by
        apply Multiset.map_id_domain;
        rintro ⟨l, ξ⟩ hlξ;
        apply LabelledFormula.labelReplace_specific_not;
        have : (w ∶ ξ) ∉ S.Γ.fmls := not_include_labelledFml_of_isFreshLabel ?_ ξ;
        rintro rfl;
        contradiction;
        apply getFreshLabel_mono (Δ := ⟨(w ∶ φ) ::ₘ S.Γ.fmls, S.Γ.rels⟩);
        . simp [Multiset.subset_cons];
        . rfl;
      have e₂ : S.Δ.fmls⟦w ↦ z⟧ = S.Δ.fmls := by
        apply Multiset.map_id_domain;
        intro ⟨l, ξ⟩ hlξ;
        apply LabelledFormula.labelReplace_specific_not;
        rintro rfl;
        have : (w ∶ ξ) ∉ S.Δ.fmls := not_include_labelledFml_of_isFreshLabel ?_ ξ;
        contradiction;
        exact Sequent.getFreshLabel_isFreshLabel₂;
      have e₃ : S.Γ.rels⟦w ↦ z⟧ = S.Γ.rels := by
        apply Multiset.map_id_domain;
        intro ⟨l₁, l₂⟩ hl;
        apply LabelTerm.labelReplace_specific_not_both;
        . rintro rfl;
          have : (w, l₂) ∉ S.Γ.rels := not_include_relTerm_of_isFreshLabel₁ ?_ l₂;
          contradiction;
          exact Sequent.getFreshLabel_isFreshLabel₁;
        . rintro rfl;
          have : (l₁, w) ∉ S.Γ.rels := not_include_relTerm_of_isFreshLabel₂ ?_ l₁;
          contradiction;
          exact Sequent.getFreshLabel_isFreshLabel₁;
      have e₄ : S.Δ.rels⟦w ↦ z⟧ = S.Δ.rels := by
        apply Multiset.map_id_domain;
        intro ⟨l₁, l₂⟩ hl;
        apply LabelTerm.labelReplace_specific_not_both;
        . rintro rfl;
          have : (w, l₂) ∉ S.Δ.rels := not_include_relTerm_of_isFreshLabel₁ ?_ l₂;
          contradiction;
          exact Sequent.getFreshLabel_isFreshLabel₂;
        . rintro rfl;
          have : (l₁, w) ∉ S.Δ.rels := not_include_relTerm_of_isFreshLabel₂ ?_ l₁;
          contradiction;
          exact Sequent.getFreshLabel_isFreshLabel₂;
      have e₅ : ((w ↦ z) y ∶ □ψ) = (y ∶ □ψ) := by
        apply LabelledFormula.labelReplace_specific_not;
        apply Ne.symm;
        apply Sequent.getFreshLabel_relΓ₁ (y := z);
        simp;
      simpa [e₁, e₂, e₃, e₄, e₅] using this;
      . apply of_isFreshLabel;
        . intro ξ;
          suffices (w ≠ z) ∧ (z ∶ ξ) ∉ S.Γ.fmls by simp; constructor <;> tauto;
          constructor;
          . apply Sequent.getFreshLabel_ne₁ (φ := φ) (by simp);
          . apply not_include_labelledFml_of_isFreshLabel hΓz ξ;
        . apply not_include_relTerm_of_isFreshLabel₁ hΓz;
        . apply not_include_relTerm_of_isFreshLabel₂ hΓz;
    . refine boxRₕ (S := ⟨(x ∶ φ) ::ₘ S.Γ.fmls, S.Γ.rels⟩ ⟹ S.Δ) (k := k) y z ψ hyz ?_ hΔz ih;
      . apply of_isFreshLabel;
        . intro ξ;
          suffices (z ≠ x) ∧ (z ∶ ξ) ∉ S.Γ.fmls by simp; constructor <;> tauto;
          constructor;
          . assumption;
          . exact not_include_labelledFml_of_isFreshLabel hΓz ξ;
        . apply not_include_relTerm_of_isFreshLabel₁ hΓz;
        . apply not_include_relTerm_of_isFreshLabel₂ hΓz;

noncomputable def wkFmlL (d : ⊢ᵍ S) : ⊢ᵍ ⟨(x ∶ φ) ::ₘ S.Γ.fmls, S.Γ.rels⟩ ⟹ S.Δ := wkFmlLₕ (d := .ofDerivation d) |>.drv

noncomputable def wkFmlLₐ (x φ) :
  ⊢ᵍ (⟨Φ, X⟩ ⟹ ⟨Ψ, Y⟩) →
  ⊢ᵍ (⟨(x ∶ φ) ::ₘ Φ, X⟩ ⟹ ⟨Ψ, Y⟩)
  := wkFmlL


noncomputable def wkRelLₕ (d : ⊢ᵍ[h] S) : ⊢ᵍ[h] ⟨S.Γ.fmls, (x, y) ::ₘ S.Γ.rels⟩ ⟹ S.Δ := by
  induction d using DerivationWithHeight.rec' generalizing x y with
  | hAtom z a => exact initAtom_memₕ z a (by simp) (by simp);
  | hBot z => exact initBot_memₕ z (by simp);
  | @hImpR S z φ ψ k d ih =>
    suffices ⊢ᵍ[k + 1] ⟨S.Γ.fmls, (x, y) ::ₘ S.Γ.rels⟩ ⟹ ⟨(z ∶ φ ➝ ψ) ::ₘ S.Δ.fmls, S.Δ.rels⟩ by simpa;
    exact impRₕ (S := ⟨S.Γ.fmls, (x, y) ::ₘ S.Γ.rels⟩ ⟹ S.Δ) z φ ψ $ ih;
  | @hImpL S z φ ψ k₁ k₂ d₁ d₂ ih₁ ih₂ =>
    suffices ⊢ᵍ[max k₁ k₂ + 1] ⟨(z ∶ φ ➝ ψ) ::ₘ S.Γ.fmls, (x, y) ::ₘ S.Γ.rels⟩ ⟹ S.Δ by simpa;
    exact impLₕ (S := ⟨S.Γ.fmls, (x, y) ::ₘ S.Γ.rels⟩ ⟹ S.Δ) z φ ψ ih₁ ih₂;
  | @hBoxL S z w φ k d ih =>
    suffices ⊢ᵍ[k + 1] ⟨(z ∶ □φ) ::ₘ S.Γ.fmls, (x, y) ::ₘ (z, w) ::ₘ S.Γ.rels⟩ ⟹ S.Δ by simpa;
    refine exchangeRelLₕ $ @boxLₕ (S := ⟨S.Γ.fmls, (x, y) ::ₘ S.Γ.rels⟩ ⟹ S.Δ) k z w φ ?_;
    exact exchangeRelLₕ ih;
  | @hBoxR S z w hzw hΓw hΔw φ k d ih =>
    by_cases ewx : w = x <;> by_cases ewy : w = y
    . subst ewx; subst ewy;
      let v : Label := ((⟨S.Γ.fmls, (w, z) ::ₘ S.Γ.rels⟩) ⟹ S.Δ).getFreshLabel;
      have := boxRₕ
        (S := ⟨S.Γ.fmls, (v, v) ::ₘ S.Γ.rels⟩ ⟹ S.Δ)
        (k := k) z w φ hzw ?_ hΔw (exchangeRelLₕ ih);
      have := @replaceLabelₕ
        (x := v) (y := w) (k := k + 1)
        (S := ⟨S.Γ.fmls, (v, v) ::ₘ S.Γ.rels⟩ ⟹ ⟨(z ∶ □φ) ::ₘ S.Δ.fmls, S.Δ.rels ⟩)
        this;
      have e₁ : S.Γ.fmls⟦v ↦ w⟧ = S.Γ.fmls := by
        apply Multiset.map_id_domain;
        rintro ⟨l, ξ⟩ hlξ;
        apply LabelledFormula.labelReplace_specific_not;
        rintro rfl;
        refine not_include_labelledFml_of_isFreshLabel ?_ ξ hlξ;
        apply getFreshLabel_mono (Δ := ⟨S.Γ.fmls, (v, v) ::ₘ S.Γ.rels⟩);
        . rfl;
        . simp [Multiset.subset_cons];
      have e₂ : S.Δ.fmls⟦v ↦ w⟧ = S.Δ.fmls := by
        apply Multiset.map_id_domain;
        rintro ⟨l, ξ⟩ hlξ;
        apply LabelledFormula.labelReplace_specific_not;
        rintro rfl;
        refine not_include_labelledFml_of_isFreshLabel ?_ ξ hlξ;
        exact Sequent.getFreshLabel_isFreshLabel₂;
      have e₃ : S.Γ.rels⟦v ↦ w⟧ = S.Γ.rels := by
        apply Multiset.map_id_domain;
        rintro ⟨l₁, l₂⟩ hl;
        apply LabelTerm.labelReplace_specific_not_both;
        . rintro rfl;
          exact not_include_relTerm_of_isFreshLabel₁ Sequent.getFreshLabel_isFreshLabel₁ l₂ hl;
        . rintro rfl;
          exact not_include_relTerm_of_isFreshLabel₂ Sequent.getFreshLabel_isFreshLabel₁ l₁ hl;
      have e₄ : S.Δ.rels⟦v ↦ w⟧ = S.Δ.rels := by
        apply Multiset.map_id_domain;
        rintro ⟨l₁, l₂⟩ hl;
        apply LabelTerm.labelReplace_specific_not_both;
        . rintro rfl;
          exact not_include_relTerm_of_isFreshLabel₁ Sequent.getFreshLabel_isFreshLabel₂ l₂ hl;
        . rintro rfl;
          exact not_include_relTerm_of_isFreshLabel₂ Sequent.getFreshLabel_isFreshLabel₂ l₁ hl;
      have e₅ : (v ↦ w) w = w := by simp; -- TODO: this should be a lemma
      have e₆ : (v ↦ w) z = z := by
        suffices v ≠ z by simp; tauto;
        exact Sequent.getFreshLabel_relΓ₂ (x := w) (y := z) (by simp);
      simpa [e₁, e₂, e₃, e₄, e₅, e₆] using this;
      . apply of_isFreshLabel;
        . apply not_include_labelledFml_of_isFreshLabel hΓw;
        . intro l;
          suffices (v ≠ w) ∧ (w, l) ∉ S.Γ.rels by simp; constructor <;> tauto;
          constructor;
          . apply Sequent.getFreshLabel_relΓ₁ (y := z) (by simp);
          . apply not_include_relTerm_of_isFreshLabel₁ hΓw;
        . intro l;
          suffices (v ≠ w) ∧ (l, w) ∉ S.Γ.rels by simp; constructor <;> tauto;
          constructor;
          . apply Sequent.getFreshLabel_relΓ₁ (y := z) (by simp);
          . apply not_include_relTerm_of_isFreshLabel₂ hΓw;
    . subst ewx;
      let v : Label := ((⟨S.Γ.fmls, (w, y) ::ₘ (w, z) ::ₘ S.Γ.rels⟩) ⟹ S.Δ).getFreshLabel;
      have := boxRₕ
        (S := ⟨S.Γ.fmls, (v, y) ::ₘ S.Γ.rels⟩ ⟹ S.Δ)
        (k := k) z w φ hzw ?_ hΔw (exchangeRelLₕ ih);
      have := @replaceLabelₕ
        (x := v) (y := w) (k := k + 1)
        (S := ⟨S.Γ.fmls, (v, y) ::ₘ S.Γ.rels⟩ ⟹ ⟨(z ∶ □φ) ::ₘ S.Δ.fmls, S.Δ.rels ⟩)
        this;
      have e₁ : S.Γ.fmls⟦v ↦ w⟧ = S.Γ.fmls := by
        apply Multiset.map_id_domain;
        rintro ⟨l, ξ⟩ hlξ;
        apply LabelledFormula.labelReplace_specific_not;
        rintro rfl;
        refine not_include_labelledFml_of_isFreshLabel ?_ ξ hlξ;
        apply getFreshLabel_mono (Δ := ⟨S.Γ.fmls, (v, y) ::ₘ S.Γ.rels⟩);
        . rfl;
        . simp [Multiset.subset_cons];
      have e₂ : S.Δ.fmls⟦v ↦ w⟧ = S.Δ.fmls := by
        apply Multiset.map_id_domain;
        rintro ⟨l, ξ⟩ hlξ;
        apply LabelledFormula.labelReplace_specific_not;
        rintro rfl;
        refine not_include_labelledFml_of_isFreshLabel ?_ ξ hlξ;
        exact Sequent.getFreshLabel_isFreshLabel₂;
      have e₃ : S.Γ.rels⟦v ↦ w⟧ = S.Γ.rels := by
        apply Multiset.map_id_domain;
        rintro ⟨l₁, l₂⟩ hl;
        apply LabelTerm.labelReplace_specific_not_both;
        . rintro rfl;
          exact not_include_relTerm_of_isFreshLabel₁ Sequent.getFreshLabel_isFreshLabel₁ l₂ hl;
        . rintro rfl;
          exact not_include_relTerm_of_isFreshLabel₂ Sequent.getFreshLabel_isFreshLabel₁ l₁ hl;
      have e₄ : S.Δ.rels⟦v ↦ w⟧ = S.Δ.rels := by
        apply Multiset.map_id_domain;
        rintro ⟨l₁, l₂⟩ hl;
        apply LabelTerm.labelReplace_specific_not_both;
        . rintro rfl;
          exact not_include_relTerm_of_isFreshLabel₁ Sequent.getFreshLabel_isFreshLabel₂ l₂ hl;
        . rintro rfl;
          exact not_include_relTerm_of_isFreshLabel₂ Sequent.getFreshLabel_isFreshLabel₂ l₁ hl;
      have e₅ : (v ↦ w) y = y := by
        suffices v ≠ y by simp; tauto;
        exact Sequent.getFreshLabel_relΓ₂ (x := w) (y := y) (by simp);
      have e₆ : (v ↦ w) z = z := by
        suffices v ≠ z by simp; tauto;
        exact Sequent.getFreshLabel_relΓ₂ (x := w) (y := z) (by simp);
      simpa [e₁, e₂, e₃, e₄, e₅, e₆] using this;
      . apply of_isFreshLabel;
        . apply not_include_labelledFml_of_isFreshLabel hΓw;
        . intro l;
          suffices (v ≠ w) ∧ (w, l) ∉ S.Γ.rels by simp; constructor <;> tauto;
          constructor;
          . apply Sequent.getFreshLabel_relΓ₁ (y := y); simp;
          . apply not_include_relTerm_of_isFreshLabel₁ hΓw;
        . intro l;
          suffices (v ≠ w) ∧ (l, w) ∉ S.Γ.rels by simp; constructor <;> tauto;
          constructor;
          . apply Sequent.getFreshLabel_relΓ₁ (y := y); simp;
          . apply not_include_relTerm_of_isFreshLabel₂ hΓw;
    . subst ewy;
      let v : Label := ((⟨S.Γ.fmls, (x, w) ::ₘ (w, z) ::ₘ S.Γ.rels⟩) ⟹ S.Δ).getFreshLabel;
      have := boxRₕ
        (S := ⟨S.Γ.fmls, (x, v) ::ₘ S.Γ.rels⟩ ⟹ S.Δ)
        (k := k) z w φ hzw ?_ hΔw (exchangeRelLₕ ih);
      have := @replaceLabelₕ
        (x := v) (y := w) (k := k + 1)
        (S := ⟨S.Γ.fmls, (x, v) ::ₘ S.Γ.rels⟩ ⟹ ⟨(z ∶ □φ) ::ₘ S.Δ.fmls, S.Δ.rels ⟩)
        this;
      have e₁ : S.Γ.fmls⟦v ↦ w⟧ = S.Γ.fmls := by
        apply Multiset.map_id_domain;
        rintro ⟨l, ξ⟩ hlξ;
        apply LabelledFormula.labelReplace_specific_not;
        rintro rfl;
        refine not_include_labelledFml_of_isFreshLabel ?_ ξ hlξ;
        apply getFreshLabel_mono (Δ := ⟨S.Γ.fmls, (x, v) ::ₘ S.Γ.rels⟩);
        . rfl;
        . simp [Multiset.subset_cons];
      have e₂ : S.Δ.fmls⟦v ↦ w⟧ = S.Δ.fmls := by
        apply Multiset.map_id_domain;
        rintro ⟨l, ξ⟩ hlξ;
        apply LabelledFormula.labelReplace_specific_not;
        rintro rfl;
        refine not_include_labelledFml_of_isFreshLabel ?_ ξ hlξ;
        exact Sequent.getFreshLabel_isFreshLabel₂;
      have e₃ : S.Γ.rels⟦v ↦ w⟧ = S.Γ.rels := by
        apply Multiset.map_id_domain;
        rintro ⟨l₁, l₂⟩ hl;
        apply LabelTerm.labelReplace_specific_not_both;
        . rintro rfl;
          exact not_include_relTerm_of_isFreshLabel₁ Sequent.getFreshLabel_isFreshLabel₁ l₂ hl;
        . rintro rfl;
          exact not_include_relTerm_of_isFreshLabel₂ Sequent.getFreshLabel_isFreshLabel₁ l₁ hl;
      have e₄ : S.Δ.rels⟦v ↦ w⟧ = S.Δ.rels := by
        apply Multiset.map_id_domain;
        rintro ⟨l₁, l₂⟩ hl;
        apply LabelTerm.labelReplace_specific_not_both;
        . rintro rfl;
          exact not_include_relTerm_of_isFreshLabel₁ Sequent.getFreshLabel_isFreshLabel₂ l₂ hl;
        . rintro rfl;
          exact not_include_relTerm_of_isFreshLabel₂ Sequent.getFreshLabel_isFreshLabel₂ l₁ hl;
      have e₅ : (v ↦ w) x = x := by
        suffices v ≠ x by simp; tauto;
        exact Sequent.getFreshLabel_relΓ₁ (x := x) (y := w) (by simp);
      have e₆ : (v ↦ w) z = z := by
        suffices v ≠ z by simp; tauto;
        exact Sequent.getFreshLabel_relΓ₂ (x := w) (y := z) (by simp);
      simpa [e₁, e₂, e₃, e₄, e₅, e₆] using this;
      . apply of_isFreshLabel;
        . apply not_include_labelledFml_of_isFreshLabel hΓw;
        . intro l;
          suffices (v ≠ w) ∧ (w, l) ∉ S.Γ.rels by simp; constructor <;> tauto;
          constructor;
          . apply Sequent.getFreshLabel_relΓ₁ (y := z); simp;
          . apply not_include_relTerm_of_isFreshLabel₁ hΓw;
        . intro l;
          suffices (v ≠ w) ∧ (l, w) ∉ S.Γ.rels by simp; constructor <;> tauto;
          constructor;
          . apply Sequent.getFreshLabel_relΓ₁ (y := z); simp;
          . apply not_include_relTerm_of_isFreshLabel₂ hΓw;
    . suffices ⊢ᵍ[k + 1] ⟨S.Γ.fmls, (x, y) ::ₘ S.Γ.rels⟩ ⟹ ⟨(z ∶ □φ) ::ₘ S.Δ.fmls, S.Δ.rels⟩ by simpa;
      refine @boxRₕ (S := ⟨S.Γ.fmls, (x, y) ::ₘ S.Γ.rels⟩ ⟹ S.Δ) k z w φ hzw ?_ hΔw ?_;
      . apply of_isFreshLabel;
        . apply not_include_labelledFml_of_isFreshLabel hΓw;
        . intro v;
          suffices (w ≠ x) ∧ (w, v) ∉ S.Γ.rels by simp; constructor <;> tauto;
          constructor;
          . assumption;
          . apply not_include_relTerm_of_isFreshLabel₁ hΓw;
        . intro v;
          suffices (w ≠ x) ∧ (v, w) ∉ S.Γ.rels by simp; constructor <;> tauto;
          constructor;
          . assumption;
          . apply not_include_relTerm_of_isFreshLabel₂ hΓw;
      . exact exchangeRelLₕ ih;

noncomputable def wkRelL (d : ⊢ᵍ S) : ⊢ᵍ ⟨S.Γ.fmls, (x, y) ::ₘ S.Γ.rels⟩ ⟹ S.Δ := wkRelLₕ (d := .ofDerivation d) |>.drv

noncomputable def wkRelLₐ (x y) :
  ⊢ᵍ (⟨Φ, X⟩ ⟹ ⟨Ψ, Y⟩) →
  ⊢ᵍ (⟨Φ, (x, y) ::ₘ X⟩ ⟹ ⟨Ψ, Y⟩)
  := wkRelL


def wkFmlRₕ (d : ⊢ᵍ[h] S) : ⊢ᵍ[h] Γ ⟹ ⟨(x ∶ φ) ::ₘ S.Δ.fmls, S.Δ.rels⟩ := by sorry

def wkFmlR (d : ⊢ᵍ S) : ⊢ᵍ Γ ⟹ ⟨(x ∶ φ) ::ₘ S.Δ.fmls, S.Δ.rels⟩ := wkFmlRₕ (d := .ofDerivation d) |>.drv


def wkRelRₕ (d : ⊢ᵍ[h] S) : ⊢ᵍ[h] Γ ⟹ ⟨S.Δ.fmls, (x, y) ::ₘ S.Δ.rels⟩ := by sorry

def wkRelR (d : ⊢ᵍ S) : ⊢ᵍ Γ ⟹ ⟨S.Δ.fmls, (x, y) ::ₘ S.Δ.rels⟩ := wkRelRₕ (d := .ofDerivation d) |>.drv


end LO.Modal.Labelled.Gentzen
