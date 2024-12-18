import Foundation.Modal.Kripke.Basic
import LabelledSystem.Basic
import Mathlib.Tactic.Abel

namespace LO.Modal

namespace Labelled

namespace Gentzen

open Formula


abbrev LabelledFormulae := Multiset LabelledFormula

namespace LabelledFormulae

abbrev labelReplace (σ : LabelReplace) (Φ : LabelledFormulae) : LabelledFormulae := Φ.map (.labelReplace σ)
notation Φ "⟦" σ "⟧" => labelReplace σ Φ

end LabelledFormulae


abbrev RelTerms := Multiset LabelTerm

namespace RelTerms

abbrev labelReplace (σ : LabelReplace) (X : RelTerms) : RelTerms := X.map (.labelReplace σ)
notation X "⟦" σ "⟧" => labelReplace σ X

end RelTerms


structure SequentPart where
  fmls : LabelledFormulae
  rels : RelTerms

namespace SequentPart

def isFreshLabel (x : Label) (Γ : SequentPart) : Prop := (x ∉ Γ.fmls.map LabelledFormula.label) ∧ (∀ y, (x, y) ∉ Γ.rels) ∧ (∀ y, (y, x) ∉ Γ.rels)

section

/-
instance : Decidable (isFreshLabel Γ x) := by
  simp [isFreshLabel];
-/

variable {x : Label} {Γ : SequentPart}

lemma not_include_labelledFml_of_isFreshLabel (h : Γ.isFreshLabel x) : ∀ φ, (x ∶ φ) ∉ Γ.fmls := by have := h.1; aesop;

lemma not_include_relTerm_of_isFreshLabel₁ (h : Γ.isFreshLabel x) : ∀ y, (x, y) ∉ Γ.rels := by have := h.2; aesop;

lemma not_include_relTerm_of_isFreshLabel₂ (h : Γ.isFreshLabel x) : ∀ y, (y, x) ∉ Γ.rels := by have := h.2.2; aesop;

lemma of_isFreshLabel
  (hFmls : ∀ φ, (x ∶ φ) ∉ Γ.fmls)
  (hRel₁ : ∀ y, (x, y) ∉ Γ.rels)
  (hRel₂ : ∀ y, (y, x) ∉ Γ.rels)
  : Γ.isFreshLabel x := by
  refine ⟨?_, hRel₁, hRel₂⟩;
  . suffices ∀ y ∈ Γ.fmls, ¬y.label = x by simpa;
    rintro ⟨y, φ⟩ hφ rfl;
    have := hFmls φ;
    contradiction;

end


section

def getFreshLabel (Γ : SequentPart) : Label :=
  letI l₁ := Γ.fmls.map LabelledFormula.label;
  letI l₂ := Γ.rels.map (λ (x, y) => max x y);
  0

variable {Γ Δ : SequentPart}

@[simp]
lemma getFreshLabel_isFreshLabel : Γ.isFreshLabel (Γ.getFreshLabel) := by sorry;

lemma getFreshLabel_ne (h : (x ∶ φ) ∈ Γ.fmls) : Γ.getFreshLabel ≠ x := by
  rintro rfl;
  exact not_include_labelledFml_of_isFreshLabel getFreshLabel_isFreshLabel φ h;

lemma getFreshLabel_rel₁ (h : (x, y) ∈ Γ.rels) : Γ.getFreshLabel ≠ x := by
  rintro rfl;
  exact not_include_relTerm_of_isFreshLabel₁ getFreshLabel_isFreshLabel y h;

lemma getFreshLabel_rel₂ (h : (x, y) ∈ Γ.rels) : Γ.getFreshLabel ≠ y := by
  rintro rfl;
  exact not_include_relTerm_of_isFreshLabel₂ getFreshLabel_isFreshLabel x h;

lemma getFreshLabel_mono (hFmls : Γ.fmls ⊆ Δ.fmls) (hRels : Γ.rels ⊆ Δ.rels) : Γ.isFreshLabel Δ.getFreshLabel := by
  apply of_isFreshLabel;
  . suffices ∀ (φ : Formula PropVar), (Δ.getFreshLabel ∶ φ) ∉ Δ.fmls by
      intro φ;
      exact Multiset.not_mem_mono hFmls $ this φ;
    apply not_include_labelledFml_of_isFreshLabel;
    simp;
  . suffices ∀ (y : Label), (Δ.getFreshLabel, y) ∉ Δ.rels by
      intro φ;
      exact Multiset.not_mem_mono hRels $ this φ;
    apply not_include_relTerm_of_isFreshLabel₁;
    simp;
  . suffices ∀ (y : Label), (y, Δ.getFreshLabel) ∉ Δ.rels by
      intro φ;
      exact Multiset.not_mem_mono hRels $ this φ;
    apply not_include_relTerm_of_isFreshLabel₂;
    simp;

end


def replaceLabel (σ : LabelReplace) (Γ : SequentPart) : SequentPart := ⟨Γ.fmls⟦σ⟧, Γ.rels⟦σ⟧⟩
notation Γ "⟦" σ "⟧" => SequentPart.replaceLabel σ Γ

@[simp]
lemma def_replaceLabel {Γ : SequentPart} {σ} : Γ⟦σ⟧ = ⟨Γ.fmls⟦σ⟧, Γ.rels⟦σ⟧⟩ := rfl


abbrev add (Γ Δ : SequentPart) : SequentPart := ⟨Γ.fmls + Δ.fmls, Γ.rels + Δ.rels⟩
instance : Add SequentPart := ⟨add⟩

end SequentPart


structure Sequent where
  Γ : SequentPart
  Δ : SequentPart

infix:50 " ⟹ " => Sequent.mk

namespace Sequent

abbrev ofFormula (φ : Formula PropVar) : Sequent := ⟨∅, ∅⟩ ⟹ ⟨{0 ∶ φ}, ∅⟩
instance : Coe (Formula PropVar) Sequent := ⟨Sequent.ofFormula⟩


abbrev replaceLabel (σ : LabelReplace) (S : Sequent) : Sequent := S.Γ⟦σ⟧ ⟹ S.Δ⟦σ⟧
notation S "⟦" σ "⟧" => Sequent.replaceLabel σ S

@[simp]
lemma def_replaceLabel {σ : LabelReplace} {S : Sequent} : S⟦σ⟧ = (S.Γ⟦σ⟧ ⟹ S.Δ⟦σ⟧) := rfl


abbrev Satisfies (M : Kripke.Model) (f : Assignment M) : Sequent → Prop := λ ⟨Γ, Δ⟩ =>
  (∀ lφ ∈ Γ.fmls, f ⊧ lφ) ∧ (∀ r ∈ Γ.rels, r.evaluated f) →
  (∃ lφ ∈ Δ.fmls, f ⊧ lφ) ∨ (∃ r ∈ Δ.rels, r.evaluated f)

namespace Satisfies

protected instance semantics {M : Kripke.Model} : Semantics Sequent (Assignment M) := ⟨fun x ↦ Satisfies M x⟩

end Satisfies


def getFreshLabel (S : Sequent) : Label := max S.Γ.getFreshLabel S.Δ.getFreshLabel

section

variable {S : Sequent}

@[simp]
lemma getFreshLabel_isFreshLabel₁ : S.Γ.isFreshLabel (S.getFreshLabel) := by
  simp [getFreshLabel];
  sorry;

@[simp]
lemma getFreshLabel_isFreshLabel₂ : S.Δ.isFreshLabel (S.getFreshLabel) := getFreshLabel_isFreshLabel₁ (S := ⟨S.Δ, S.Γ⟩)

lemma getFreshLabel_ne₁ (h : (x ∶ φ) ∈ S.Γ.fmls) : S.getFreshLabel ≠ x := by
  rintro rfl;
  exact SequentPart.not_include_labelledFml_of_isFreshLabel getFreshLabel_isFreshLabel₁ φ h;

lemma getFreshLabel_ne₂ (h : (x ∶ φ) ∈ S.Δ.fmls) : S.getFreshLabel ≠ x := by
  rintro rfl;
  exact SequentPart.not_include_labelledFml_of_isFreshLabel getFreshLabel_isFreshLabel₂ φ h;


lemma getFreshLabel_relΓ₁ (h : (x, y) ∈ S.Γ.rels) : S.getFreshLabel ≠ x := by
  rintro rfl;
  exact SequentPart.not_include_relTerm_of_isFreshLabel₁ getFreshLabel_isFreshLabel₁ y h;

lemma getFreshLabel_relΓ₂ (h : (x, y) ∈ S.Γ.rels) : S.getFreshLabel ≠ y := by
  rintro rfl;
  exact SequentPart.not_include_relTerm_of_isFreshLabel₂ getFreshLabel_isFreshLabel₁ x h;

lemma getFreshLabel_relΔ₁ (h : (x, y) ∈ S.Δ.rels) : S.getFreshLabel ≠ x := by
  rintro rfl;
  exact SequentPart.not_include_relTerm_of_isFreshLabel₁ getFreshLabel_isFreshLabel₂ y h;

lemma getFreshLabel_relΔ₂ (h : (x, y) ∈ S.Δ.rels) : S.getFreshLabel ≠ y := by
  rintro rfl;
  exact SequentPart.not_include_relTerm_of_isFreshLabel₂ getFreshLabel_isFreshLabel₂ x h;


end

end Sequent

-- variable {S : Sequent}
-- variable {Γ Γ₁ Γ₂ Δ Δ₁ Δ₂ : SequentPart}

inductive Derivation : Sequent → Type _
| initAtom {S : Sequent} (x) (a) : Derivation (⟨(x ∶ atom a) ::ₘ S.Γ.fmls, S.Γ.rels⟩ ⟹ ⟨(x ∶ atom a) ::ₘ S.Δ.fmls, S.Δ.rels⟩)
| initBot {S : Sequent} (x) : Derivation (⟨(x ∶ ⊥) ::ₘ S.Γ.fmls, S.Γ.rels⟩ ⟹ S.Δ)
| impL {S : Sequent} (x) (φ ψ) :
    Derivation (S.Γ ⟹ ⟨(x ∶ φ) ::ₘ S.Δ.fmls, S.Δ.rels⟩) →
    Derivation (⟨(x ∶ ψ) ::ₘ S.Γ.fmls, S.Γ.rels⟩ ⟹ S.Δ) →
    Derivation (⟨(x ∶ φ ➝ ψ) ::ₘ S.Γ.fmls, S.Γ.rels⟩ ⟹ S.Δ)
| impR {S : Sequent} (x) (φ ψ) :
    Derivation (⟨(x ∶ φ) ::ₘ S.Γ.fmls, S.Γ.rels⟩ ⟹ ⟨(x ∶ ψ) ::ₘ S.Δ.fmls, S.Δ.rels⟩) →
    Derivation (S.Γ ⟹ ⟨(x ∶ φ ➝ ψ) ::ₘ S.Δ.fmls, S.Δ.rels⟩)
| boxL {S : Sequent} (x y) (φ) :
    Derivation (⟨(x ∶ □φ) ::ₘ (y ∶ φ) ::ₘ S.Γ.fmls, (x, y) ::ₘ S.Γ.rels⟩ ⟹ S.Δ) →
    Derivation (⟨(x ∶ □φ) ::ₘ S.Γ.fmls, (x, y) ::ₘ S.Γ.rels⟩ ⟹ S.Δ)
| boxR {S : Sequent} (x y) (φ) :
    x ≠ y → S.Γ.isFreshLabel y → S.Δ.isFreshLabel y →
    Derivation (⟨S.Γ.fmls, (x, y) ::ₘ S.Γ.rels⟩ ⟹ ⟨(y ∶ φ) ::ₘ S.Δ.fmls, S.Δ.rels⟩) →
    Derivation (S.Γ ⟹ ⟨(x ∶ □φ) ::ₘ S.Δ.fmls, S.Δ.rels⟩)
prefix:40 "⊢ᵍ " => Derivation

export Derivation (initAtom initBot impL impR boxL boxR)

abbrev Derivable (S : Sequent) : Prop := Nonempty (⊢ᵍ S)
prefix:40 "⊢ᵍ! " => Derivable

section

open SequentPart

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

end


namespace Derivation

def height {S : Sequent} : ⊢ᵍ S → ℕ
  | initAtom _ _ => 0
  | initBot _ => 0
  | impL _ _ _ d₁ d₂ => max d₁.height d₂.height + 1
  | impR _ _ _ d => d.height + 1
  | boxL _ _ _ d => d.height + 1
  | boxR _ _ _ _ _ _ d => d.height + 1

@[simp] lemma initAtom_height : (Derivation.initAtom (S := S) x a).height = 0 := rfl

@[simp] lemma initBot_height : (Derivation.initBot (S := S) x).height = 0 := rfl

@[simp] lemma impL_height : (impL x φ ψ d₁ d₂).height = max d₁.height d₂.height + 1 := rfl

@[simp] lemma impR_height : (impR x φ ψ d).height = d.height + 1 := rfl

@[simp] lemma boxL_height : (boxL x y φ d).height = d.height + 1 := rfl

@[simp] lemma boxR_height : (boxR x y φ h₁ h₂ h₃ d).height = d.height + 1 := rfl

end Derivation

structure DerivationWithHeight (S : Sequent) (k : ℕ) where
  drv : ⊢ᵍ S
  height_le : drv.height ≤ k
notation:80 "⊢ᵍ[" h "] " S => DerivationWithHeight S h

namespace DerivationWithHeight

def ofDerivation (d : ⊢ᵍ S) : ⊢ᵍ[d.height] S := ⟨d, by omega⟩

def ofTaller (h : k ≤ l) : (⊢ᵍ[k] S) → (⊢ᵍ[l] S) := λ ⟨d, a⟩ => ⟨d, by omega⟩

def ofTaller₀ (d : ⊢ᵍ[0] S) : (⊢ᵍ[k] S) := ofTaller (by omega) d

variable {Γ Δ : SequentPart}

lemma ofZero (d : ⊢ᵍ[0] Γ ⟹ Δ) : (∃ x a, (x ∶ .atom a) ∈ Γ.fmls ∧ (x ∶ .atom a) ∈ Δ.fmls) ∨ (∃ x, (x ∶ ⊥) ∈ Γ.fmls) := by
  obtain ⟨d, height_le⟩ := d;
  cases d with
  | initAtom y a => left; use y, a; simp;
  | initBot y => right; use y; simp;
  | _ => simp [Derivation.height] at height_le;

end DerivationWithHeight

abbrev DerivableWithHeight (S : Sequent) (h : ℕ) : Prop := Nonempty (⊢ᵍ[h] S)
notation:80 "⊢ᵍ[" h "]! " S => DerivableWithHeight S h


section

variable {S : Sequent}

def initAtomₕ (x a) : ⊢ᵍ[k] (⟨(x ∶ atom a) ::ₘ S.Γ.fmls, S.Γ.rels⟩ ⟹ ⟨(x ∶ atom a) ::ₘ S.Δ.fmls, S.Δ.rels⟩) := ⟨initAtom x a, by simp⟩

def initBotₕ (x) : ⊢ᵍ[k] (⟨(x ∶ ⊥) ::ₘ S.Γ.fmls, S.Γ.rels⟩ ⟹ S.Δ) := ⟨initBot x, by simp⟩

def impRₕ (x φ ψ) :
  (⊢ᵍ[h] (⟨(x ∶ φ) ::ₘ S.Γ.fmls, S.Γ.rels⟩ ⟹ ⟨(x ∶ ψ) ::ₘ S.Δ.fmls, S.Δ.rels⟩)) →
  (⊢ᵍ[h + 1] (S.Γ ⟹ ⟨(x ∶ φ ➝ ψ) ::ₘ S.Δ.fmls, S.Δ.rels⟩)) := by
  rintro ⟨d, hk⟩;
  exact ⟨impR x φ ψ d, by simpa [impR]⟩

def impLₕ (x φ ψ) :
  (⊢ᵍ[k₁] (S.Γ ⟹ ⟨(x ∶ φ) ::ₘ S.Δ.fmls, S.Δ.rels⟩)) →
  (⊢ᵍ[k₂] (⟨(x ∶ ψ) ::ₘ S.Γ.fmls, S.Γ.rels⟩ ⟹ S.Δ)) →
  (⊢ᵍ[max k₁ k₂ + 1] (⟨(x ∶ φ ➝ ψ) ::ₘ S.Γ.fmls, S.Γ.rels⟩ ⟹ S.Δ)) := by
  rintro ⟨d₁, hk₁⟩ ⟨d₂, hk₂⟩;
  exact ⟨
    @impL S x φ ψ d₁ d₂,
    by simp [impL]; omega;
  ⟩;

def boxLₕ (x y φ) :
  (⊢ᵍ[k] (⟨(x ∶ □φ) ::ₘ (y ∶ φ) ::ₘ S.Γ.fmls, (x, y) ::ₘ S.Γ.rels⟩ ⟹ S.Δ)) →
  (⊢ᵍ[k + 1] (⟨(x ∶ □φ) ::ₘ S.Γ.fmls, (x, y) ::ₘ S.Γ.rels⟩ ⟹ S.Δ)) := by
  rintro ⟨d, hk⟩;
  exact ⟨boxL x y φ d, by simpa [boxL]⟩

def boxRₕ (x y φ)
  (h₁ : x ≠ y)
  (h₂ : S.Γ.isFreshLabel y)
  (h₃ : S.Δ.isFreshLabel y) :
  (⊢ᵍ[k] (⟨S.Γ.fmls, (x, y) ::ₘ S.Γ.rels⟩ ⟹ ⟨(y ∶ φ) ::ₘ S.Δ.fmls, S.Δ.rels⟩)) →
  (⊢ᵍ[k + 1] (S.Γ ⟹ ⟨(x ∶ □φ) ::ₘ S.Δ.fmls, S.Δ.rels⟩)) := by
  rintro ⟨d, hk⟩;
  exact ⟨boxR x y φ h₁ h₂ h₃ d, by simpa [boxR]⟩

end


namespace DerivationWithHeight

noncomputable def rec'
  (motive : ∀ (S k), (⊢ᵍ[k] S) → Sort*)
  (hAtom :
    {S : Sequent} →
    (x : Label) →
    (a : PropVar) →
    (k : ℕ) →
    motive (⟨(x ∶ atom a) ::ₘ S.Γ.fmls, S.Γ.rels⟩ ⟹ ⟨(x ∶ atom a) ::ₘ S.Δ.fmls, S.Δ.rels⟩) k (initAtomₕ x a)
  )
  (hBot :
    {S : Sequent} →
    (x : Label) →
    (k : ℕ) →
    motive (⟨(x ∶ ⊥) ::ₘ S.Γ.fmls, S.Γ.rels⟩ ⟹ S.Δ) k (initBotₕ x)
  )
  (hImpR :
    {S : Sequent} →
    (x : Label) →
    (φ ψ : Formula PropVar) →
    (k : ℕ) →
    (d : ⊢ᵍ[k] ⟨(x ∶ φ) ::ₘ S.Γ.fmls, S.Γ.rels⟩ ⟹ ⟨(x ∶ ψ) ::ₘ S.Δ.fmls, S.Δ.rels⟩) →
    motive _ k d →
    motive _ (k + 1) (impRₕ x φ ψ d)
  )
  (hImpL :
    {S : Sequent} →
    (x : Label) →
    (φ ψ : Formula PropVar) →
    (k₁ k₂ : ℕ) →
    (d₁ : ⊢ᵍ[k₁] S.Γ ⟹ ⟨(x ∶ φ) ::ₘ S.Δ.fmls, S.Δ.rels⟩) →
    (d₂ : ⊢ᵍ[k₂] ⟨(x ∶ ψ) ::ₘ S.Γ.fmls, S.Γ.rels⟩ ⟹ S.Δ) →
    motive _ k₁ d₁ →
    motive _ k₂ d₂ →
    motive _ (max k₁ k₂ + 1) (impLₕ x φ ψ d₁ d₂)
  )
  (hBoxL :
    {S : Sequent} →
    (x y : Label) →
    (φ : Formula PropVar) →
    (k : ℕ) →
    (d : ⊢ᵍ[k] ⟨(x ∶ □φ) ::ₘ (y ∶ φ) ::ₘ S.Γ.fmls, (x, y) ::ₘ S.Γ.rels⟩ ⟹ S.Δ) →
    motive _ k d →
    motive _ (k + 1) (boxLₕ x y φ d)
  )
  (hBoxR :
    {S : Sequent} →
    (x y : Label) →
    (hxy : x ≠ y) →
    (hΓ : S.Γ.isFreshLabel y) →
    (hΔ : S.Δ.isFreshLabel y) →
    (φ : Formula PropVar) →
    (k : ℕ) →
    (d : ⊢ᵍ[k] ⟨S.Γ.fmls, (x, y) ::ₘ S.Γ.rels⟩ ⟹ ⟨(y ∶ φ) ::ₘ S.Δ.fmls, S.Δ.rels⟩) →
    motive _ k d →
    motive _ (k + 1) (boxRₕ x y φ hxy hΓ hΔ d)
  )
  : ∀ {S k}, (d : ⊢ᵍ[k] S) → motive S k d
  := by
  rintro S k ⟨d, hk⟩;
  induction d generalizing k with
  | @initAtom S x a =>
    exact @hAtom S x a k;
  | @initBot S x =>
    exact @hBot S x k;
  | impR x φ ψ d ih =>
    by_cases k = 0;
    . simp at hk;
      omega;
    . convert hImpR x φ ψ (k - 1) ⟨d, by simp at hk; omega⟩ ?_;
      . omega;
      . exact ih $ by simp at hk; omega;
  | impL x φ ψ d₁ d₂ ih₁ ih₂ =>
    by_cases k = 0;
    . simp at hk;
      omega;
    . convert hImpL x φ ψ (k - 1) (k - 1) ⟨d₁, by simp at hk; omega⟩ ⟨d₂, by simp at hk; omega⟩ ?_ ?_;
      . omega;
      . exact ih₁ $ by simp at hk; omega;
      . exact ih₂ $ by simp at hk; omega;
  | boxL x y φ d ih =>
    by_cases k = 0;
    . simp at hk;
      omega;
    . convert hBoxL x y φ (k - 1) ⟨d, by simp at hk; omega⟩ ?_;
      . omega;
      . exact ih $ by simp at hk; omega;
  | boxR x y φ hxy hΓy hΔy d ih =>
    by_cases k = 0;
    . simp at hk;
      omega;
    . convert hBoxR x y hxy hΓy hΔy φ (k - 1) ⟨d, by simp at hk; omega⟩ ?_;
      . omega;
      . exact ih $ by simp at hk; omega;

end DerivationWithHeight



section

def initAtom_memₕ
  {k : ℕ} (x a)
  (h₁ : (x ∶ atom a) ∈ S.Γ.fmls)
  (h₂ : (x ∶ atom a) ∈ S.Δ.fmls)
  : ⊢ᵍ[k] S := by
  suffices ⊢ᵍ[k] (⟨S.Γ.fmls, S.Γ.rels⟩ ⟹ ⟨S.Δ.fmls, S.Δ.rels⟩) by simpa;
  rw [←(Multiset.cons_erase h₁), ←(Multiset.cons_erase h₂)];
  exact ⟨initAtom (S := ⟨S.Γ.fmls.erase (x ∶ .atom a), S.Γ.rels⟩ ⟹ ⟨S.Δ.fmls.erase (x ∶ .atom a), S.Δ.rels⟩) x a, by simp⟩

def initAtom_mem
  (x a)
  (h₁ : (x ∶ atom a) ∈ S.Γ.fmls)
  (h₂ : (x ∶ atom a) ∈ S.Δ.fmls)
  : ⊢ᵍ S := initAtom_memₕ (k := 0) x a h₁ h₂ |>.drv


def initBot_memₕ
  {k : ℕ}
  (x)
  (h : (x ∶ ⊥) ∈ S.Γ.fmls)
  : ⊢ᵍ[k] S := by
  suffices ⊢ᵍ[k] (⟨S.Γ.fmls, S.Γ.rels⟩ ⟹ S.Δ) by simpa;
  rw [←(Multiset.cons_erase h)];
  exact ⟨initBot (S := ⟨S.Γ.fmls.erase (x ∶ ⊥), S.Γ.rels⟩ ⟹ S.Δ) x, by simp⟩

def initBot_mem
  (x)
  (h : (x ∶ ⊥) ∈ S.Γ.fmls)
  : ⊢ᵍ S := initBot_memₕ (k := 0) x h |>.drv

end


section

open Sequent

variable {S : Sequent}

def initFml (x φ)
  : ⊢ᵍ (⟨(x ∶ φ) ::ₘ S.Γ.fmls, S.Γ.rels⟩ ⟹ ⟨(x ∶ φ) ::ₘ S.Δ.fmls, S.Δ.rels⟩) := by
  induction φ using Formula.rec' generalizing S x with
  | hatom a => apply initAtom_mem x a (by simp) (by simp);
  | hfalsum => apply initBot_mem x (by simp);
  | himp φ ψ ihφ ihψ =>
    apply impR (S := ⟨(x ∶ φ ➝ ψ) ::ₘ S.Γ.fmls, S.Γ.rels⟩ ⟹ S.Δ);
    rw [Multiset.cons_swap];
    apply impL (S := ⟨(x ∶ φ) ::ₘ S.Γ.fmls, S.Γ.rels⟩ ⟹ ⟨(x ∶ ψ) ::ₘ S.Δ.fmls, S.Δ.rels⟩);
    . simpa using ihφ (S := S.Γ ⟹ ⟨(x ∶ ψ) ::ₘ S.Δ.fmls, S.Δ.rels⟩) x;
    . simpa using ihψ (S := ⟨(x ∶ φ) ::ₘ S.Γ.fmls, S.Γ.rels⟩ ⟹ S.Δ) x;
  | hbox φ ih =>
    let y := (⟨(x ∶ □φ) ::ₘ S.Γ.fmls, S.Γ.rels⟩ ⟹ S.Δ).getFreshLabel;
    apply boxR (φ := φ) (x := x) (y := y) (S := ⟨(x ∶ □φ) ::ₘ S.Γ.fmls, S.Γ.rels⟩ ⟹ S.Δ) ?_ ?_ ?_;
    apply boxL (S := ⟨S.Γ.fmls, S.Γ.rels⟩ ⟹ ⟨(y ∶ φ) ::ₘ S.Δ.fmls, S.Δ.rels⟩);
    rw [Multiset.cons_swap];
    exact ih (S := ⟨(x ∶ □φ) ::ₘ S.Γ.fmls, (x, y) ::ₘ S.Γ.rels⟩ ⟹ S.Δ) y;
    . exact (getFreshLabel_ne₁ (x := x) (φ := □φ) (by simp)).symm
    . exact getFreshLabel_isFreshLabel₁;
    . exact getFreshLabel_isFreshLabel₂;

def initFml_mem (x φ) (hΓ : (x ∶ φ) ∈ S.Γ.fmls) (hΔ : (x ∶ φ) ∈ S.Δ.fmls)
  : ⊢ᵍ S := by
  suffices ⊢ᵍ (⟨S.Γ.fmls, S.Γ.rels⟩ ⟹ ⟨S.Δ.fmls, S.Δ.rels⟩) by simpa;
  rw [←(Multiset.cons_erase hΓ), ←(Multiset.cons_erase hΔ)];
  exact initFml (S := ⟨S.Γ.fmls.erase (x ∶ φ), S.Γ.rels⟩ ⟹  ⟨S.Δ.fmls.erase (x ∶ φ), S.Δ.rels⟩) x φ;

end


section

variable {S : Sequent}
variable {x y z : Label} {φ ψ ξ : Formula PropVar}

def exchangeFmlLₕ :
  (⊢ᵍ[k] (⟨(x ∶ φ) ::ₘ (y ∶ ψ) ::ₘ Φ, X⟩ ⟹ Δ)) →
  (⊢ᵍ[k] (⟨(y ∶ ψ) ::ₘ (x ∶ φ) ::ₘ Φ, X⟩ ⟹ Δ))
  := by
  suffices (x ∶ φ) ::ₘ (y ∶ ψ) ::ₘ Φ = (y ∶ ψ) ::ₘ (x ∶ φ) ::ₘ Φ by
    rw [this];
    tauto;
  simp_rw [←Multiset.singleton_add];
  abel;

def exchangeFmlL
  (d : ⊢ᵍ (⟨(x ∶ φ) ::ₘ (y ∶ ψ) ::ₘ Φ, X⟩ ⟹ Δ))
  : ⊢ᵍ (⟨(y ∶ ψ) ::ₘ (x ∶ φ) ::ₘ Φ, X⟩ ⟹ Δ)
  := exchangeFmlLₕ (k := d.height) ⟨d, by simp⟩ |>.drv


def exchangeFml₃Lₕ :
  (⊢ᵍ[k] (⟨(x ∶ φ) ::ₘ (y ∶ ψ) ::ₘ (z ∶ ξ) ::ₘ Φ, X⟩ ⟹ Δ)) →
  (⊢ᵍ[k] (⟨(y ∶ ψ) ::ₘ (z ∶ ξ) ::ₘ (x ∶ φ) ::ₘ Φ, X⟩ ⟹ Δ))
  := by
  suffices (x ∶ φ) ::ₘ (y ∶ ψ) ::ₘ (z ∶ ξ) ::ₘ Φ = (y ∶ ψ) ::ₘ (z ∶ ξ) ::ₘ (x ∶ φ) ::ₘ Φ by
    rw [this];
    tauto;
  simp_rw [←Multiset.singleton_add];
  abel;

def exchangeFml₃L
  (d : ⊢ᵍ (⟨(x ∶ φ) ::ₘ (y ∶ ψ) ::ₘ (z ∶ ξ) ::ₘ Φ, X⟩ ⟹ Δ))
  : ⊢ᵍ (⟨(y ∶ ψ) ::ₘ (z ∶ ξ) ::ₘ (x ∶ φ) ::ₘ Φ, X⟩ ⟹ Δ)
  := exchangeFml₃Lₕ (k := d.height) ⟨d, by simp⟩ |>.drv

end


end Gentzen

end Labelled

end LO.Modal
