import Foundation.Modal.Kripke.Basic
import ModalTableau.Basic

namespace LO.Modal

namespace Labelled

namespace Gentzen

open Formula

structure SequentPart where
  fmls : Multiset LabelledFormula
  rels : Multiset LabelTerm

namespace SequentPart

def isFreshLabel (x : Label) (Γ : SequentPart) : Prop := (x ∉ Γ.fmls.map LabelledFormula.label) ∧ (∀ y, (x, y) ∉ Γ.rels) ∧ (∀ y, (y, x) ∉ Γ.rels)

/-
instance : Decidable (isFreshLabel Γ x) := by
  simp [isFreshLabel];
-/

variable {x : Label} {Γ : SequentPart}

lemma not_include_labelledFml_of_isFreshLabel (h : Γ.isFreshLabel x) : ∀ φ, (x ∶ φ) ∉ Γ.fmls := by have := h.1; aesop;

lemma not_include_relTerm_of_isFreshLabel₁ (h : Γ.isFreshLabel x) : ∀ y, (x, y) ∉ Γ.rels := by have := h.2; aesop;

lemma not_include_relTerm_of_isFreshLabel₂ (h : Γ.isFreshLabel x) : ∀ y, (y, x) ∉ Γ.rels := by have := h.2.2; aesop;

end SequentPart


structure Sequent where
  pre : SequentPart
  pos : SequentPart

infix:50 " ⟹ " => Sequent.mk

namespace Sequent

abbrev Satisfies (M : Kripke.Model) (f : Assignment M) : Sequent → Prop := λ ⟨Γ, Δ⟩ =>
  (∀ lφ ∈ Γ.fmls, f ⊧ lφ) ∧ (∀ r ∈ Γ.rels, r.evaluated f) →
  (∃ lφ ∈ Δ.fmls, f ⊧ lφ) ∨ (∃ r ∈ Δ.rels, r.evaluated f)

namespace Satisfies

protected instance semantics {M : Kripke.Model} : Semantics Sequent (Assignment M) := ⟨fun x ↦ Satisfies M x⟩

end Satisfies

end Sequent


inductive Derivation : Sequent → Type _
| axA {Γ Δ : SequentPart} {x} {a} : Derivation (⟨(x ∶ atom a) ::ₘ Γ.fmls, Γ.rels⟩ ⟹ ⟨(x ∶ atom a) ::ₘ Δ.fmls, Δ.rels⟩)
| axBot {Γ Δ : SequentPart} {x} : Derivation (⟨(x ∶ ⊥) ::ₘ  Γ.fmls, Γ.rels⟩ ⟹ Δ)
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
prefix:70 "⊢ᵍ " => Derivation

export Derivation (axA axBot impL impR boxL boxR)

abbrev Derivable (S : Sequent) : Prop := Nonempty (⊢ᵍ S)
prefix:70 "⊢ᵍ! " => Derivable


section height

def Derivation.height {S : Sequent} : ⊢ᵍ S → ℕ
  | axA => 1
  | axBot => 1
  | impL d₁ d₂ => max d₁.height d₂.height + 1
  | impR d => d.height + 1
  | boxL d => d.height + 1
  | boxR _ _ _ d => d.height + 1

end height

def axF {Γ Δ : SequentPart} {x} {φ} : ⊢ᵍ (⟨(x ∶ φ) ::ₘ Γ.fmls, Γ.rels⟩ ⟹ ⟨(x ∶ φ) ::ₘ Δ.fmls, Δ.rels⟩) := by
  induction φ using Formula.rec' generalizing Γ Δ x with
  | hatom a => exact axA
  | hfalsum => exact axBot
  | himp φ ψ ihφ ihψ =>
    apply impR;
    simpa [Multiset.cons_swap] using impL ihφ ihψ;
  | hbox φ ih =>
    letI y := x + 1;
    apply boxR (y := y) (by simp [y]) (by sorry) (by sorry);
    apply boxL;
    simpa [Multiset.cons_swap] using ih (Γ := ⟨(x ∶ □φ) ::ₘ Γ.fmls, _ ::ₘ Γ.rels⟩);

def axiomK : ⊢ᵍ ⟨⟨∅, ∅⟩, ⟨{0 ∶ □(φ ➝ ψ) ➝ □φ ➝ □ψ}, ∅⟩⟩ := by
  apply impR (Δ := ⟨_, _⟩);
  apply impR;
  apply boxR (y := 1) (by simp) (by simp [SequentPart.isFreshLabel]) (by simp [SequentPart.isFreshLabel]);
  suffices ⊢ᵍ (⟨(0 ∶ □φ) ::ₘ {0 ∶ □(φ ➝ ψ)}, {(0, 1)}⟩ ⟹ ⟨{1 ∶ ψ}, ∅⟩) by simpa;
  apply boxL (Γ := ⟨_, _⟩);
  suffices ⊢ᵍ (⟨(0 ∶ □(φ ➝ ψ)) ::ₘ (1 ∶ φ) ::ₘ {(0 ∶ □φ)}, {(0, 1)}⟩ ⟹ ⟨{1 ∶ ψ}, ∅⟩) by
    have e : (0 ∶ □(φ ➝ ψ)) ::ₘ (1 ∶ φ) ::ₘ {0 ∶ □φ} = (0 ∶ □φ) ::ₘ (1 ∶ φ) ::ₘ {0 ∶ □(φ ➝ ψ)} := by sorry;
    simpa [e];
  apply boxL (x := 0) (φ := φ ➝ ψ) (Γ := ⟨{1 ∶ φ, 0 ∶ □φ}, _⟩);
  suffices ⊢ᵍ (⟨(1 ∶ φ ➝ ψ) ::ₘ {1 ∶ φ, 0 ∶ □φ, 0 ∶ □(φ ➝ ψ)}, {(0, 1)}⟩ ⟹ ⟨{1 ∶ ψ}, ∅⟩) by
    have e : (0 ∶ □(φ ➝ ψ)) ::ₘ (1 ∶ φ ➝ ψ) ::ₘ (1 ∶ φ) ::ₘ {0 ∶ □φ} = (1 ∶ φ ➝ ψ) ::ₘ {1 ∶ φ, 0 ∶ □φ, 0 ∶ □(φ ➝ ψ)} := by sorry;
    simpa [e];
  apply impL (Γ := ⟨_, _⟩);
  . simpa using axF (Γ := ⟨_, _⟩) (Δ := ⟨_, _⟩);
  . simpa using axF (Γ := ⟨_, _⟩) (Δ := ⟨_, _⟩);

end Gentzen



end Labelled

end LO.Modal
