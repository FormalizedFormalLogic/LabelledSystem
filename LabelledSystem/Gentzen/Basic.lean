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
  Γ : SequentPart
  Δ : SequentPart

infix:50 " ⟹ " => Sequent.mk

namespace Sequent

abbrev ofFormula (φ : Formula ℕ) : Sequent := ⟨∅, ∅⟩ ⟹ ⟨{0 ∶ φ}, ∅⟩
instance : Coe (Formula ℕ) Sequent := ⟨Sequent.ofFormula⟩


abbrev replaceLabel (σ : Label → Label) (S : Sequent) : Sequent := ⟨S.Γ⟦σ⟧, S.Δ⟦σ⟧⟩
notation S "⟦" σ "⟧" => Sequent.replaceLabel σ S


abbrev Satisfies (M : Kripke.Model) (f : Assignment M) : Sequent → Prop := λ ⟨Γ, Δ⟩ =>
  (∀ lφ ∈ Γ.fmls, f ⊧ lφ) ∧ (∀ r ∈ Γ.rels, r.evaluated f) →
  (∃ lφ ∈ Δ.fmls, f ⊧ lφ) ∨ (∃ r ∈ Δ.rels, r.evaluated f)

namespace Satisfies

protected instance semantics {M : Kripke.Model} : Semantics Sequent (Assignment M) := ⟨fun x ↦ Satisfies M x⟩

end Satisfies

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

end Derivation

structure DerivationWithHeight (S : Sequent) (k : ℕ) where
  drv : ⊢ᵍ S
  height_le : drv.height ≤ k
notation:40 "⊢ᵍ[" h "] " S => DerivationWithHeight S h

namespace DerivationWithHeight

def ofDerivation (d : ⊢ᵍ S) : ⊢ᵍ[d.height] S := ⟨d, by omega⟩

def ofTaller (h : k ≤ l) : (⊢ᵍ[k] S) → (⊢ᵍ[l] S) := λ ⟨d, a⟩ => ⟨d, by omega⟩

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
notation:40 "⊢ᵍ[" h "]! " S => DerivableWithHeight S h

end Height


variable {S : Sequent}
variable {Γ Γ₁ Γ₂ Δ Δ₁ Δ₂ : SequentPart}

open SequentPart

section

def initAtomₕ' (x a) (h₁ : (x ∶ atom a) ∈ S.Γ.fmls) (h₂ : (x ∶ atom a) ∈ S.Δ.fmls) : ⊢ᵍ[0] S := by
  suffices ⊢ᵍ[0] (⟨S.Γ.fmls, S.Γ.rels⟩ ⟹ ⟨S.Δ.fmls, S.Δ.rels⟩) by simpa;
  rw [←(Multiset.cons_erase h₁), ←(Multiset.cons_erase h₂)];
  exact ⟨initAtom (S := ⟨S.Γ.fmls.erase (x ∶ .atom a), S.Γ.rels⟩ ⟹ ⟨S.Δ.fmls.erase (x ∶ .atom a), S.Δ.rels⟩) x a, by simp⟩

def initAtom' (x a) (h₁ : (x ∶ atom a) ∈ S.Γ.fmls) (h₂ : (x ∶ atom a) ∈ S.Δ.fmls) : ⊢ᵍ S := initAtomₕ' x a h₁ h₂ |>.drv


def initBotₕ' (x) (h : (x ∶ ⊥) ∈ S.Γ.fmls) : ⊢ᵍ[0] S := by
  suffices ⊢ᵍ[0] (⟨S.Γ.fmls, S.Γ.rels⟩ ⟹ S.Δ) by simpa;
  rw [←(Multiset.cons_erase h)];
  exact ⟨initBot (S := ⟨S.Γ.fmls.erase (x ∶ ⊥), S.Γ.rels⟩ ⟹ S.Δ) x, by simp⟩

def initBot' (x) (h : (x ∶ ⊥) ∈ S.Γ.fmls) : ⊢ᵍ S := initBotₕ' x h |>.drv


def impL₂ : ⊢ᵍ (Γ ⟹ ⟨(x ∶ φ) ::ₘ Δ.fmls, Δ.rels⟩) → ⊢ᵍ (⟨(x ∶ ψ) ::ₘ Γ.fmls, Γ.rels⟩ ⟹ Δ) → ⊢ᵍ (⟨(x ∶ φ ➝ ψ) ::ₘ Γ.fmls, Γ.rels⟩ ⟹ Δ)
  := impL (S := Γ ⟹ Δ) x φ ψ


def impR₂ : ⊢ᵍ (⟨(x ∶ φ) ::ₘ Γ.fmls, Γ.rels⟩ ⟹ ⟨(x ∶ ψ) ::ₘ Δ.fmls, Δ.rels⟩) → ⊢ᵍ (Γ ⟹ ⟨(x ∶ φ ➝ ψ) ::ₘ Δ.fmls, Δ.rels⟩)
  := impR (S := Γ ⟹ Δ) x φ ψ


def boxL₂ : ⊢ᵍ (⟨(x ∶ □φ) ::ₘ (y ∶ φ) ::ₘ Γ.fmls, (x, y) ::ₘ Γ.rels⟩ ⟹ Δ) → ⊢ᵍ (⟨(x ∶ □φ) ::ₘ Γ.fmls, (x, y) ::ₘ Γ.rels⟩ ⟹ Δ)
  := boxL (S := Γ ⟹ Δ) x y φ


def boxR₂ : x ≠ y → Γ.isFreshLabel y → Δ.isFreshLabel y → ⊢ᵍ (⟨Γ.fmls, (x, y) ::ₘ Γ.rels⟩ ⟹ ⟨(y ∶ φ) ::ₘ Δ.fmls, Δ.rels⟩) → ⊢ᵍ (Γ ⟹ ⟨(x ∶ □φ) ::ₘ Δ.fmls, Δ.rels⟩)
  := boxR (S := Γ ⟹ Δ) x y φ

end

section

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
    apply boxR₂ (y := getFreshLabel₂ ⟨(x ∶ □φ) ::ₘ Γ.fmls, Γ.rels⟩ Δ)
      (getFreshLabel₂_ne₁ (x := x) (φ := □φ) (by simp)).symm
      getFreshLabel₂_isFreshLabel₁
      getFreshLabel₂_isFreshLabel₂;
    apply boxL₂;
    simpa [Multiset.cons_swap] using ih (Γ := ⟨(x ∶ □φ) ::ₘ Γ.fmls, _ ::ₘ Γ.rels⟩);

def initFml₂' (x φ) (hΓ : (x ∶ φ) ∈ Γ.fmls) (hΔ : (x ∶ φ) ∈ Δ.fmls) : ⊢ᵍ Γ ⟹ Δ := by
  suffices ⊢ᵍ (⟨Γ.fmls, Γ.rels⟩ ⟹ ⟨Δ.fmls, Δ.rels⟩) by simpa;
  rw [←(Multiset.cons_erase hΓ), ←(Multiset.cons_erase hΔ)];
  simpa using initFml₂ (Γ := ⟨Γ.fmls.erase (x ∶ φ), _⟩) (Δ := ⟨Δ.fmls.erase (x ∶ φ), _⟩);

def initFml (x φ) : ⊢ᵍ (⟨(x ∶ φ) ::ₘ S.Γ.fmls, S.Γ.rels⟩ ⟹ ⟨(x ∶ φ) ::ₘ S.Δ.fmls, S.Δ.rels⟩) := initFml₂

def initFml' (x φ) (h₁ : (x ∶ φ) ∈ S.Γ.fmls) (h₂ : (x ∶ φ) ∈ S.Δ.fmls) : ⊢ᵍ S := initFml₂' x φ h₁ h₂

end



section ReplaceLabel

open DerivationWithHeight

noncomputable def replaceLabelₕAux (d : ⊢ᵍ[k] S) (σ : Label → Label) : ⊢ᵍ[k] S⟦σ⟧ := by
  obtain ⟨d, kh⟩ := d;
  induction d with
  | initAtom y a =>
    exact ofTaller (by omega) $ initAtomₕ' (σ y) a
      (by simp [Sequent.replaceLabel, SequentPart.replaceLabel, LabelledFormula.labelReplace])
      (by simp [Sequent.replaceLabel, SequentPart.replaceLabel, LabelledFormula.labelReplace]);
  | initBot y =>
    exact ofTaller (by omega) $ initBotₕ' (σ y)
      (by simp [Sequent.replaceLabel, SequentPart.replaceLabel, LabelledFormula.labelReplace]);
  | impL d₁ d₂ ih₁ ih₂ => sorry;
  | impR x φ ψ d ih =>
    sorry;
  | boxL d ih => sorry;
  | boxR _ _ _ d ih => sorry;

def replaceLabelₕ (d : ⊢ᵍ[h] Γ ⟹ Δ) (σ : Label → Label) : ⊢ᵍ[h] Γ⟦σ⟧ ⟹ Δ⟦σ⟧ := by sorry;

def replaceLabel (d : ⊢ᵍ Γ ⟹ Δ) (σ : Label → Label) : ⊢ᵍ Γ⟦σ⟧ ⟹ Δ⟦σ⟧ := replaceLabelₕ (.ofDerivation d) σ |>.drv

end ReplaceLabel


section Weakening

open DerivationWithHeight

noncomputable def wkFmlLₕAux (d : ⊢ᵍ[k] S) : ⊢ᵍ[k] ⟨(x ∶ φ) ::ₘ S.Γ.fmls, S.Γ.rels⟩ ⟹ S.Δ := by
  obtain ⟨d, kh⟩ := d;
  induction d with
  | initAtom y a => exact ofTaller (by omega) $ initAtomₕ' y a (by simp) (by simp);
  | initBot y => exact ofTaller (by omega) $ initBotₕ' y (by simp);
  | _ => sorry;

def wkFmlLₕ (d : ⊢ᵍ[k] Γ ⟹ Δ) : ⊢ᵍ[k] ⟨(x ∶ φ) ::ₘ Γ.fmls, Γ.rels⟩ ⟹ Δ := by
  obtain ⟨d, kh⟩ := d;
  cases d with
  | initAtom y a => exact ofTaller (by omega) $ initAtomₕ' y a (by simp) (by simp);
  | initBot y => exact ofTaller (by omega) $ initBotₕ' y (by simp);
  | _ => sorry;

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
