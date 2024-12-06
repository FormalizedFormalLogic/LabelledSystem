import Foundation.Modal.Kripke.Basic
import LabelledSystem.Basic

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

end


section

def getFreshLabel₁ (Γ : SequentPart) : Label :=
  letI l₁ := Γ.fmls.map LabelledFormula.label;
  letI l₂ := Γ.rels.map (λ (x, y) => max x y);
  0

def getFreshLabel₂ (Γ Δ : SequentPart) : Label := max Γ.getFreshLabel₁ Δ.getFreshLabel₁

variable {Γ Δ : SequentPart}

lemma getFreshLabel₁_isFreshLabel : Γ.isFreshLabel (Γ.getFreshLabel₁) := by sorry;

lemma getFreshLabel₁_ne (h : (x ∶ φ) ∈ Γ.fmls) : Γ.getFreshLabel₁ ≠ x := by
  rintro rfl;
  have := not_include_labelledFml_of_isFreshLabel getFreshLabel₁_isFreshLabel (Γ := Γ) φ;
  contradiction;

@[simp]
lemma getFreshLabel₂_isFreshLabel₁ : Γ.isFreshLabel (getFreshLabel₂ Γ Δ) := by
  simp [getFreshLabel₂];
  sorry;

@[simp]
lemma getFreshLabel₂_isFreshLabel₂ : Δ.isFreshLabel (getFreshLabel₂ Γ Δ) := getFreshLabel₂_isFreshLabel₁

lemma getFreshLabel₂_ne₁ (h : (x ∶ φ) ∈ Γ.fmls) : getFreshLabel₂ Γ Δ ≠ x := by
  rintro rfl;
  have : (getFreshLabel₂ Γ Δ ∶ φ) ∉ Γ.fmls := not_include_labelledFml_of_isFreshLabel getFreshLabel₂_isFreshLabel₁ φ;
  contradiction;

lemma getFreshLabel₂_ne₂ (h : (x ∶ φ) ∈ Δ.fmls) : getFreshLabel₂ Γ Δ ≠ x := by
  rintro rfl;
  have : (getFreshLabel₂ Γ Δ ∶ φ) ∉ Δ.fmls := not_include_labelledFml_of_isFreshLabel getFreshLabel₂_isFreshLabel₂ φ;
  contradiction;

end

abbrev replaceLabel (σ : Label → Label) (Γ : SequentPart) : SequentPart :=
  ⟨Γ.fmls.map (LabelledFormula.labelReplace σ), Γ.rels.map (LabelTerm.replace σ)⟩
notation Γ "⟦" σ "⟧" => SequentPart.replaceLabel σ Γ

abbrev add (Γ Δ : SequentPart) : SequentPart := ⟨Γ.fmls + Δ.fmls, Γ.rels + Δ.rels⟩
instance : Add SequentPart := ⟨add⟩

end SequentPart


structure Sequent where
  pre : SequentPart
  pos : SequentPart

infix:50 " ⟹ " => Sequent.mk

namespace Sequent

abbrev ofFormula (φ : Formula ℕ) : Sequent := ⟨∅, ∅⟩ ⟹ ⟨{0 ∶ φ}, ∅⟩
instance : Coe (Formula ℕ) Sequent := ⟨Sequent.ofFormula⟩

abbrev Satisfies (M : Kripke.Model) (f : Assignment M) : Sequent → Prop := λ ⟨Γ, Δ⟩ =>
  (∀ lφ ∈ Γ.fmls, f ⊧ lφ) ∧ (∀ r ∈ Γ.rels, r.evaluated f) →
  (∃ lφ ∈ Δ.fmls, f ⊧ lφ) ∨ (∃ r ∈ Δ.rels, r.evaluated f)

namespace Satisfies

protected instance semantics {M : Kripke.Model} : Semantics Sequent (Assignment M) := ⟨fun x ↦ Satisfies M x⟩

end Satisfies

end Sequent


inductive Derivation : Sequent → Type _
| initAtom {Γ Δ : SequentPart} {x} {a} : Derivation (⟨(x ∶ atom a) ::ₘ Γ.fmls, Γ.rels⟩ ⟹ ⟨(x ∶ atom a) ::ₘ Δ.fmls, Δ.rels⟩)
| initBot {Γ Δ : SequentPart} {x} : Derivation (⟨(x ∶ ⊥) ::ₘ Γ.fmls, Γ.rels⟩ ⟹ Δ)
| impL {Γ Δ : SequentPart} {x} {φ ψ} :
    Derivation (Γ ⟹ ⟨(x ∶ φ) ::ₘ Δ.fmls, Δ.rels⟩) →
    Derivation (⟨(x ∶ ψ) ::ₘ Γ.fmls, Γ.rels⟩ ⟹ Δ) →
    Derivation (⟨(x ∶ φ ➝ ψ) ::ₘ Γ.fmls, Γ.rels⟩ ⟹ Δ)
| impR {Γ Δ : SequentPart} {x} {φ ψ} :
    Derivation (⟨(x ∶ φ) ::ₘ Γ.fmls, Γ.rels⟩ ⟹ ⟨(x ∶ ψ) ::ₘ Δ.fmls, Δ.rels⟩) →
    Derivation (Γ ⟹ ⟨(x ∶ φ ➝ ψ) ::ₘ Δ.fmls, Δ.rels⟩)
| boxL {Γ Δ : SequentPart} {x y} {φ} :
    Derivation (⟨(x ∶ □φ) ::ₘ (y ∶ φ) ::ₘ Γ.fmls, (x, y) ::ₘ Γ.rels⟩ ⟹ Δ) →
    Derivation (⟨(x ∶ □φ) ::ₘ Γ.fmls, (x, y) ::ₘ Γ.rels⟩ ⟹ Δ)
| boxR {Γ Δ : SequentPart} {x y} {φ} :
    x ≠ y → Γ.isFreshLabel y → Δ.isFreshLabel y →
    Derivation (⟨Γ.fmls, (x, y) ::ₘ Γ.rels⟩ ⟹ ⟨(y ∶ φ) ::ₘ Δ.fmls, Δ.rels⟩) →
    Derivation (Γ ⟹ ⟨(x ∶ □φ) ::ₘ Δ.fmls, Δ.rels⟩)
prefix:40 "⊢ᵍ " => Derivation

export Derivation (initAtom initBot impL impR boxL boxR)

abbrev Derivable (S : Sequent) : Prop := Nonempty (⊢ᵍ S)
prefix:40 "⊢ᵍ! " => Derivable


section Height

def Derivation.height {S : Sequent} : ⊢ᵍ S → ℕ
  | initAtom => 0
  | initBot => 0
  | impL d₁ d₂ => max d₁.height d₂.height + 1
  | impR d => d.height + 1
  | boxL d => d.height + 1
  | boxR _ _ _ d => d.height + 1

structure DerivationWithHeight (S : Sequent) (h : ℕ) where
  drv : ⊢ᵍ S
  height : drv.height = h
notation:40 "⊢ᵍ[" h "] " S => DerivationWithHeight S h

namespace DerivationWithHeight

def ofDerivation (d : ⊢ᵍ S) : ⊢ᵍ[d.height] S := ⟨d, rfl⟩

variable {Γ Δ : SequentPart}

lemma ofZero (d : ⊢ᵍ[0] Γ ⟹ Δ) : (∃ x a, (x ∶ .atom a) ∈ Γ.fmls) ∨ (∃ x, (x ∶ ⊥) ∈ Γ.fmls) := by
  cases d.drv with
  | @initAtom _ _ y a =>
    left;
    use y, a;
    simp;
  | @initBot _ _ y =>
    right;
    use y;
    simp;
  | _ => sorry;

end DerivationWithHeight


abbrev DerivableWithHeight (S : Sequent) (h : ℕ) : Prop := Nonempty (⊢ᵍ[h] S)
notation:40 "⊢ᵍ[ " h " ]! " S => DerivableWithHeight S h

end Height



variable {Γ Γ₁ Γ₂ Δ Δ₁ Δ₂ : SequentPart}

open SequentPart

section

end


def initFml : ⊢ᵍ (⟨(x ∶ φ) ::ₘ Γ.fmls, Γ.rels⟩ ⟹ ⟨(x ∶ φ) ::ₘ Δ.fmls, Δ.rels⟩) := by
  induction φ using Formula.rec' generalizing Γ Δ x with
  | hatom a => exact initAtom
  | hfalsum => exact initBot
  | himp φ ψ ihφ ihψ =>
    apply impR;
    simpa [Multiset.cons_swap] using impL ihφ ihψ;
  | hbox φ ih =>
    apply boxR (y := getFreshLabel₂ ⟨(x ∶ □φ) ::ₘ Γ.fmls, Γ.rels⟩ Δ)
      (getFreshLabel₂_ne₁ (x := x) (φ := □φ) (by simp)).symm
      getFreshLabel₂_isFreshLabel₁
      getFreshLabel₂_isFreshLabel₂;
    apply boxL;
    simpa [Multiset.cons_swap] using ih (Γ := ⟨(x ∶ □φ) ::ₘ Γ.fmls, _ ::ₘ Γ.rels⟩);

def initFml' (x φ) (hΓ : (x ∶ φ) ∈ Γ.fmls) (hΔ : (x ∶ φ) ∈ Δ.fmls) : ⊢ᵍ Γ ⟹ Δ := by
  suffices ⊢ᵍ (⟨Γ.fmls, Γ.rels⟩ ⟹ ⟨Δ.fmls, Δ.rels⟩) by simpa;
  have eΓ := Multiset.cons_erase hΓ;
  have eΔ := Multiset.cons_erase hΔ;
  rw [←eΓ, ←eΔ];
  simpa using initFml (Γ := ⟨Γ.fmls.erase (x ∶ φ), _⟩) (Δ := ⟨Δ.fmls.erase (x ∶ φ), _⟩);

section ReplaceLabel

def replaceLabelₕ (d : ⊢ᵍ[h] Γ ⟹ Δ) (σ : Label → Label) : ⊢ᵍ[h] Γ⟦σ⟧ ⟹ Δ⟦σ⟧ := by sorry;

def replaceLabel (d : ⊢ᵍ Γ ⟹ Δ) (σ : Label → Label) : ⊢ᵍ Γ⟦σ⟧ ⟹ Δ⟦σ⟧ := replaceLabelₕ (.ofDerivation d) σ |>.drv

end ReplaceLabel


section Weakening

def wkFmlLₕ (d : ⊢ᵍ[h] Γ ⟹ Δ) : ⊢ᵍ[h] ⟨(x ∶ φ) ::ₘ Γ.fmls, Γ.rels⟩ ⟹ Δ := by
  sorry;
  /-

  induction h with

  | zero =>
    cases d.drv with
    | @initAtom Γ Δ x a =>
      sorry;
    | boxR => sorry
    | _ => sorry
  | succ n => sorry;
  -/

def wkFmlL (d : ⊢ᵍ Γ ⟹ Δ) : ⊢ᵍ ⟨(x ∶ φ) ::ₘ Γ.fmls, Γ.rels⟩ ⟹ Δ := wkFmlLₕ (d := .ofDerivation d) |>.drv


def wkRelLₕ (d : ⊢ᵍ[h] Γ ⟹ Δ) : ⊢ᵍ[h] ⟨Γ.fmls, (x, y) ::ₘ Γ.rels⟩ ⟹ Δ := by sorry

def wkRelL (d : ⊢ᵍ Γ ⟹ Δ) : ⊢ᵍ ⟨Γ.fmls, (x, y) ::ₘ Γ.rels⟩ ⟹ Δ := wkRelLₕ (d := .ofDerivation d) |>.drv


def wkFmlRₕ (d : ⊢ᵍ[h] Γ ⟹ Δ) : ⊢ᵍ[h] Γ ⟹ ⟨(x ∶ φ) ::ₘ Δ.fmls, Δ.rels⟩ := by sorry

def wkFmlR (d : ⊢ᵍ Γ ⟹ Δ) : ⊢ᵍ Γ ⟹ ⟨(x ∶ φ) ::ₘ Δ.fmls, Δ.rels⟩ := wkFmlRₕ (d := .ofDerivation d) |>.drv


def wkRelRₕ (d : ⊢ᵍ[h] Γ ⟹ Δ) : ⊢ᵍ[h] Γ ⟹ ⟨Δ.fmls, (x, y) ::ₘ Δ.rels⟩ := by sorry

def wkRelR (d : ⊢ᵍ Γ ⟹ Δ) : ⊢ᵍ Γ ⟹ ⟨Δ.fmls, (x, y) ::ₘ Δ.rels⟩ := wkRelRₕ (d := .ofDerivation d) |>.drv

end Weakening



section Inv

def implyRInvₕ (d : ⊢ᵍ[h] (Γ ⟹ ⟨(x ∶ φ ➝ ψ) ::ₘ Δ.fmls, Δ.rels⟩)) : ⊢ᵍ[h] (⟨(x ∶ φ) ::ₘ Γ.fmls, Γ.rels⟩ ⟹ ⟨(x ∶ ψ) ::ₘ Δ.fmls, Δ.rels⟩) := by sorry

def implyRInv (d : ⊢ᵍ (Γ ⟹ ⟨(x ∶ φ ➝ ψ) ::ₘ Δ.fmls, Δ.rels⟩)) : ⊢ᵍ (⟨(x ∶ φ) ::ₘ Γ.fmls, Γ.rels⟩ ⟹ ⟨(x ∶ ψ) ::ₘ Δ.fmls, Δ.rels⟩) := implyRInvₕ (d := .ofDerivation d) |>.drv

end Inv


section Cut

def cutRel (d₁ : ⊢ᵍ Γ₁ ⟹ ⟨Δ₁.fmls, (x, y) ::ₘ Δ₁.rels⟩) (d₂ : ⊢ᵍ ⟨Γ₂.fmls, (x, y) ::ₘ Γ₂.rels⟩ ⟹ Δ₂) : ⊢ᵍ (Γ₁ + Γ₂) ⟹ (Δ₁ + Δ₂) := by
  sorry

def cutFml (d₁ : ⊢ᵍ Γ₁ ⟹ ⟨(x ∶ φ) ::ₘ Δ₁.fmls, Δ₁.rels⟩) (d₂ : ⊢ᵍ ⟨(x ∶ φ) ::ₘ Γ₂.fmls, Γ₂.rels⟩ ⟹ Δ₂) : ⊢ᵍ (Γ₁ + Γ₂) ⟹ (Δ₁ + Δ₂) := by
  sorry

end Cut


end Gentzen

end Labelled

end LO.Modal
