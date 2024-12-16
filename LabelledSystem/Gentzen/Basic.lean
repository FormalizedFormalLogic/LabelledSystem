import Foundation.Modal.Kripke.Basic
import LabelledSystem.Basic
import Mathlib.Tactic.Abel

namespace LO.Modal

namespace Labelled

namespace Gentzen

open Formula

structure SequentPart where
  fmls : Multiset LabelledFormula
  rels : Multiset LabelTerm

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
  have := not_include_labelledFml_of_isFreshLabel getFreshLabel_isFreshLabel (Γ := Γ) φ;
  contradiction;

lemma getFreshLabel_mono (hFmls : Γ.fmls ⊆ Δ.fmls) (hRels : Γ.rels ⊆ Δ.rels) : Γ.isFreshLabel Δ.getFreshLabel := by
  apply of_isFreshLabel;
  . suffices ∀ (φ : Formula ℕ), (Δ.getFreshLabel ∶ φ) ∉ Δ.fmls by
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


def replaceLabel (σ : LabelReplace) (Γ : SequentPart) : SequentPart :=
  ⟨Γ.fmls.map (.labelReplace σ), Γ.rels.map (.labelReplace σ)⟩
notation Γ "⟦" σ "⟧" => SequentPart.replaceLabel σ Γ

@[simp]
lemma def_replaceLabel {Γ : SequentPart} {σ} : Γ⟦σ⟧ = ⟨Γ.fmls.map (.labelReplace σ), Γ.rels.map (.labelReplace σ)⟩ := rfl


abbrev add (Γ Δ : SequentPart) : SequentPart := ⟨Γ.fmls + Δ.fmls, Γ.rels + Δ.rels⟩
instance : Add SequentPart := ⟨add⟩

end SequentPart


structure Sequent where
  Γ : SequentPart
  Δ : SequentPart

infix:50 " ⟹ " => Sequent.mk

namespace Sequent

abbrev ofFormula (φ : Formula ℕ) : Sequent := ⟨∅, ∅⟩ ⟹ ⟨{0 ∶ φ}, ∅⟩
instance : Coe (Formula ℕ) Sequent := ⟨Sequent.ofFormula⟩


abbrev replaceLabel (σ : Label → Label) (S : Sequent) : Sequent := ⟨S.Γ⟦σ⟧, S.Δ⟦σ⟧⟩
notation S "⟦" σ "⟧" => Sequent.replaceLabel σ S

@[simp]
lemma def_replaceLabel {σ : LabelReplace} {S : Sequent} : S⟦σ⟧ = ⟨S.Γ⟦σ⟧, S.Δ⟦σ⟧⟩ := rfl


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
  have : (S.getFreshLabel ∶ φ) ∉ S.Γ.fmls := SequentPart.not_include_labelledFml_of_isFreshLabel getFreshLabel_isFreshLabel₁ φ;
  contradiction;

lemma getFreshLabel_ne₂ (h : (x ∶ φ) ∈ S.Δ.fmls) : S.getFreshLabel ≠ x := by
  rintro rfl;
  have : (S.getFreshLabel ∶ φ) ∉ S.Δ.fmls := SequentPart.not_include_labelledFml_of_isFreshLabel getFreshLabel_isFreshLabel₂ φ;
  contradiction;

end

end Sequent


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


section Height

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

noncomputable def induc
  (motive : ∀ S k, (⊢ᵍ[k] S) → Sort*)
  : ∀ S k, (d : ⊢ᵍ[k] S) → motive S k d
  := by
  rintro S h ⟨d, h_le⟩;
  induction d with
  | initAtom x a =>
    sorry;
  | initBot =>
    sorry;
  | impL d₁ d₂ ih₁ ih₂ =>
    sorry;
  | impR d ih =>
    sorry;
  | boxL d ih =>
    sorry;
  | boxR _ _ _ d ih =>
    sorry;

end DerivationWithHeight


abbrev DerivableWithHeight (S : Sequent) (h : ℕ) : Prop := Nonempty (⊢ᵍ[h] S)
notation:80 "⊢ᵍ[" h "]! " S => DerivableWithHeight S h

end Height


variable {S : Sequent}
variable {Γ Γ₁ Γ₂ Δ Δ₁ Δ₂ : SequentPart}

open SequentPart

section

def initAtomₕ' {k : ℕ} (x a) (h₁ : (x ∶ atom a) ∈ S.Γ.fmls) (h₂ : (x ∶ atom a) ∈ S.Δ.fmls) : ⊢ᵍ[k] S := by
  suffices ⊢ᵍ[k] (⟨S.Γ.fmls, S.Γ.rels⟩ ⟹ ⟨S.Δ.fmls, S.Δ.rels⟩) by simpa;
  rw [←(Multiset.cons_erase h₁), ←(Multiset.cons_erase h₂)];
  exact ⟨initAtom (S := ⟨S.Γ.fmls.erase (x ∶ .atom a), S.Γ.rels⟩ ⟹ ⟨S.Δ.fmls.erase (x ∶ .atom a), S.Δ.rels⟩) x a, by simp⟩

def initAtom' (x a) (h₁ : (x ∶ atom a) ∈ S.Γ.fmls) (h₂ : (x ∶ atom a) ∈ S.Δ.fmls) : ⊢ᵍ S := initAtomₕ' (k := 0) x a h₁ h₂ |>.drv


def initBotₕ' {k : ℕ} (x) (h : (x ∶ ⊥) ∈ S.Γ.fmls) : ⊢ᵍ[k] S := by
  suffices ⊢ᵍ[k] (⟨S.Γ.fmls, S.Γ.rels⟩ ⟹ S.Δ) by simpa;
  rw [←(Multiset.cons_erase h)];
  exact ⟨initBot (S := ⟨S.Γ.fmls.erase (x ∶ ⊥), S.Γ.rels⟩ ⟹ S.Δ) x, by simp⟩

def initBot' (x) (h : (x ∶ ⊥) ∈ S.Γ.fmls) : ⊢ᵍ S := initBotₕ' (k := 0) x h |>.drv


def impL₂ :
  ⊢ᵍ (Γ ⟹ ⟨(x ∶ φ) ::ₘ Δ.fmls, Δ.rels⟩) →
  ⊢ᵍ (⟨(x ∶ ψ) ::ₘ Γ.fmls, Γ.rels⟩ ⟹ Δ) →
  ⊢ᵍ (⟨(x ∶ φ ➝ ψ) ::ₘ Γ.fmls, Γ.rels⟩ ⟹ Δ)
  := impL (S := Γ ⟹ Δ) x φ ψ

def impLₕ :
  (⊢ᵍ[k₁] (Γ ⟹ ⟨(x ∶ φ) ::ₘ Δ.fmls, Δ.rels⟩)) →
  (⊢ᵍ[k₂] (⟨(x ∶ ψ) ::ₘ Γ.fmls, Γ.rels⟩ ⟹ Δ)) →
  (⊢ᵍ[max k₁ k₂ + 1] (⟨(x ∶ φ ➝ ψ) ::ₘ Γ.fmls, Γ.rels⟩ ⟹ Δ)) := by
  rintro ⟨d₁, hk₁⟩ ⟨d₂, hk₂⟩;
  exact ⟨impL₂ d₁ d₂, by dsimp [impL₂]; omega⟩;


def impR₂ :
  ⊢ᵍ (⟨(x ∶ φ) ::ₘ Γ.fmls, Γ.rels⟩ ⟹ ⟨(x ∶ ψ) ::ₘ Δ.fmls, Δ.rels⟩) →
  ⊢ᵍ (Γ ⟹ ⟨(x ∶ φ ➝ ψ) ::ₘ Δ.fmls, Δ.rels⟩)
  := impR (S := Γ ⟹ Δ) x φ ψ

def impRₕ :
  (⊢ᵍ[h] (⟨(x ∶ φ) ::ₘ Γ.fmls, Γ.rels⟩ ⟹ ⟨(x ∶ ψ) ::ₘ Δ.fmls, Δ.rels⟩)) →
  (⊢ᵍ[h + 1] (Γ ⟹ ⟨(x ∶ φ ➝ ψ) ::ₘ Δ.fmls, Δ.rels⟩)) := by
  rintro ⟨d, hk⟩;
  exact ⟨impR₂ d, by simpa [impR₂]⟩


def boxL₂ :
  ⊢ᵍ (⟨(x ∶ □φ) ::ₘ (y ∶ φ) ::ₘ Γ.fmls, (x, y) ::ₘ Γ.rels⟩ ⟹ Δ) →
  ⊢ᵍ (⟨(x ∶ □φ) ::ₘ Γ.fmls, (x, y) ::ₘ Γ.rels⟩ ⟹ Δ)
  := boxL (S := Γ ⟹ Δ) x y φ

def boxLₕ :
  (⊢ᵍ[k] (⟨(x ∶ □φ) ::ₘ (y ∶ φ) ::ₘ Γ.fmls, (x, y) ::ₘ Γ.rels⟩ ⟹ Δ)) →
  (⊢ᵍ[k + 1] (⟨(x ∶ □φ) ::ₘ Γ.fmls, (x, y) ::ₘ Γ.rels⟩ ⟹ Δ)) := by
  rintro ⟨d, hk⟩;
  exact ⟨boxL₂ d, by simpa [boxL₂]⟩


def boxR₂ : x ≠ y → Γ.isFreshLabel y → Δ.isFreshLabel y →
  ⊢ᵍ (⟨Γ.fmls, (x, y) ::ₘ Γ.rels⟩ ⟹ ⟨(y ∶ φ) ::ₘ Δ.fmls, Δ.rels⟩) →
  ⊢ᵍ (Γ ⟹ ⟨(x ∶ □φ) ::ₘ Δ.fmls, Δ.rels⟩)
  := boxR (S := Γ ⟹ Δ) x y φ

def boxRₕ (hxy : x ≠ y) (hΓ : Γ.isFreshLabel y) (hΔ : Δ.isFreshLabel y) :
  (⊢ᵍ[h] (⟨Γ.fmls, (x, y) ::ₘ Γ.rels⟩ ⟹ ⟨(y ∶ φ) ::ₘ Δ.fmls, Δ.rels⟩)) →
  (⊢ᵍ[h + 1] (Γ ⟹ ⟨(x ∶ □φ) ::ₘ Δ.fmls, Δ.rels⟩)) := by
  rintro ⟨d, hk⟩;
  exact ⟨boxR₂ hxy hΓ hΔ d, by simpa [boxR₂]⟩

end

section

open Sequent

def initFml₂ : ⊢ᵍ (⟨(x ∶ φ) ::ₘ Γ.fmls, Γ.rels⟩ ⟹ ⟨(x ∶ φ) ::ₘ Δ.fmls, Δ.rels⟩) := by
  induction φ using Formula.rec' generalizing Γ Δ x with
  | hatom a => apply initAtom' x a (by simp) (by simp);
  | hfalsum => apply initBot' x (by simp);
  | himp φ ψ ihφ ihψ =>
    apply impR₂;
    rw [Multiset.cons_swap];
    apply impL₂ (Γ := ⟨(x ∶ φ) ::ₘ Γ.fmls, Γ.rels⟩) (Δ := ⟨(x ∶ ψ) ::ₘ Δ.fmls, Δ.rels⟩);
    . simpa using ihφ (Δ := ⟨(x ∶ ψ) ::ₘ Δ.fmls, Δ.rels⟩);
    . simpa using ihψ (Γ := ⟨(x ∶ φ) ::ₘ Γ.fmls, Γ.rels⟩);
  | hbox φ ih =>
    apply boxR₂ (y := (⟨(x ∶ □φ) ::ₘ Γ.fmls, Γ.rels⟩ ⟹ Δ).getFreshLabel)
      (getFreshLabel_ne₁ (x := x) (φ := □φ) (by simp)).symm
      getFreshLabel_isFreshLabel₁
      getFreshLabel_isFreshLabel₂;
    apply boxL₂;
    simpa [Multiset.cons_swap] using ih (Γ := ⟨(x ∶ □φ) ::ₘ Γ.fmls, _ ::ₘ Γ.rels⟩);

def initFml₂' (x φ) (hΓ : (x ∶ φ) ∈ Γ.fmls) (hΔ : (x ∶ φ) ∈ Δ.fmls) : ⊢ᵍ Γ ⟹ Δ := by
  suffices ⊢ᵍ (⟨Γ.fmls, Γ.rels⟩ ⟹ ⟨Δ.fmls, Δ.rels⟩) by simpa;
  rw [←(Multiset.cons_erase hΓ), ←(Multiset.cons_erase hΔ)];
  simpa using initFml₂ (Γ := ⟨Γ.fmls.erase (x ∶ φ), _⟩) (Δ := ⟨Δ.fmls.erase (x ∶ φ), _⟩);

def initFml (x φ) : ⊢ᵍ (⟨(x ∶ φ) ::ₘ S.Γ.fmls, S.Γ.rels⟩ ⟹ ⟨(x ∶ φ) ::ₘ S.Δ.fmls, S.Δ.rels⟩) := initFml₂

def initFml' (x φ) (h₁ : (x ∶ φ) ∈ S.Γ.fmls) (h₂ : (x ∶ φ) ∈ S.Δ.fmls) : ⊢ᵍ S := initFml₂' x φ h₁ h₂

end


section

variable {x y z : Label} {φ ψ ξ : Formula ℕ}

def exchangeFmlLₕ :
  (⊢ᵍ[k] (⟨(x ∶ φ) ::ₘ (y ∶ ψ) ::ₘ Γ.fmls, Γ.rels⟩ ⟹ Δ)) →
  (⊢ᵍ[k] (⟨(y ∶ ψ) ::ₘ (x ∶ φ) ::ₘ Γ.fmls, Γ.rels⟩ ⟹ Δ))
  := by
  suffices (x ∶ φ) ::ₘ (y ∶ ψ) ::ₘ Γ.fmls = (y ∶ ψ) ::ₘ (x ∶ φ) ::ₘ Γ.fmls by
    rw [this];
    tauto;
  simp_rw [←Multiset.singleton_add]
  abel;

def exchangeFml₃Lₕ :
  (⊢ᵍ[k] (⟨(x ∶ φ) ::ₘ (y ∶ ψ) ::ₘ (z ∶ ξ) ::ₘ Γ.fmls, Γ.rels⟩ ⟹ Δ)) →
  (⊢ᵍ[k] (⟨(y ∶ ψ) ::ₘ (z ∶ ξ) ::ₘ (x ∶ φ) ::ₘ Γ.fmls, Γ.rels⟩ ⟹ Δ))
  := by
  suffices (x ∶ φ) ::ₘ (y ∶ ψ) ::ₘ (z ∶ ξ) ::ₘ Γ.fmls = (y ∶ ψ) ::ₘ (z ∶ ξ) ::ₘ (x ∶ φ) ::ₘ Γ.fmls by
    rw [this];
    tauto;
  simp_rw [←Multiset.singleton_add];
  abel;

end

end Gentzen

end Labelled

end LO.Modal
