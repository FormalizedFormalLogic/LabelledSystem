import Foundation.Modal.NNFormula

namespace LO.Modal

open NNFormula

variable {α β : Type*}


namespace Tableau

abbrev Label := ℕ
abbrev PropVar := ℕ

structure LabelledFormula where
  label : Label
  formula : NNFormula PropVar

namespace LabelledFormula

notation:max l " ∶ " φ => LabelledFormula.mk l φ

section toStr

def toStr (lf : LabelledFormula) : String := s!"{lf.label} : {lf.formula.toStr}"

instance : Repr (LabelledFormula) := ⟨λ t _ => toStr t⟩
instance : ToString (LabelledFormula) := ⟨toStr⟩

#eval (0 ∶ atom 1 ➝ atom 2)

end toStr

end LabelledFormula


abbrev RelTerm := Label × Label

namespace RelTerm

notation a " ≺ " b => (a, b)

def toStr (rt : RelTerm) : String := s!"{rt.1} ≺ {rt.2}"
instance : Repr RelTerm := ⟨λ t _ => toStr t⟩
instance : ToString RelTerm := ⟨toStr⟩

end RelTerm


inductive Node where
  | fml : LabelledFormula → Bool → Node
  | rel : RelTerm → Node

def Node.toStr : Node → String
  | .fml lf b => s!"{if b then "✅" else "❌"} : {lf}"
  | .rel rt   => s!"_ : {rt}"
instance : Repr (Node) := ⟨λ t _ => t.toStr⟩
instance : ToString (Node) := ⟨Node.toStr⟩

#eval ([.rel (1, 2), .rel (2, 4), .fml ⟨0, ⊤⟩ true] : List Node)

inductive Branch where
  | zero : Node → (n : ℕ) → (Fin n → List (Fin n)) → Branch
  | one  : Node → (n : ℕ) → (Fin n → List (Fin n)) → Branch → Branch
  | two  : Node → (n : ℕ) → (Fin n → List (Fin n)) → Branch → Branch → Branch

namespace Branch

-- ┝  └  ┑

def _root_.String.repeat (s : String) : ℕ → String
  | 0 => ""
  | n+1 => s ++ s.repeat n

abbrev Indenter := List (Fin 2)
def Indenter.toStr (I : Indenter) : String := I.reverse.map (λ n => s!"{n}") |> String.intercalate "."
instance : ToString Indenter := ⟨Indenter.toStr⟩

#eval ([0, 0, 0] : Indenter)

def toStrIndent (s : Indenter) : Branch → String
  | .zero N _ _ => s!"{s} - {N}"
  | .one N _ _ B => s!"{s} - {N}\n{B.toStrIndent s}"
  | .two N _ _ B₁ B₂ => s!"{s} - {N}\n{B₁.toStrIndent (0 :: s)}\n{B₂.toStrIndent (1 :: s)}"

def toStr (p : Branch) : String := p.toStrIndent [0]
instance : Repr (Branch) := ⟨λ t _ => t.toStr⟩
instance : ToString (Branch) := ⟨toStr⟩

end Branch

/-
#eval
  Branch.one (.fml (1 ∶ ⊤) true) $
  Branch.two (.fml (1 ∶ ⊤) true)
    (
      .one (.fml (3 ∶ ((atom 1) ⋎ (atom 3))) true) 3 (λ n => 1 < n) $
      .zero (.fml (4 ∶ ((atom 1) ⋏ (atom 3))) true)
    )
    (
      .zero (.fml (4 ∶ ((atom 1) ⋏ (atom 3))) true)
    )

/-
```
(1)
┃ ✅ : 1 : ⊤
┃ ✅ : 2 : ⊤
┣━┓ (1.1)
┃ ┃ ✅ : 3 : (+1 ∨ +3)
┃ ┃ ✅ : 5 : ⊤
┃ ┣━┓ (1.1.1)
┃ ┃ ┃ ✅ : 6 : ⊤
┃ ┃ ┗ _ : 1 ≺ 2
┃ ┗━┓ (1.1.2)
┃   ┃ ✅ : 8 : ⊤
┃   ┗ _ : 2 ≺ 3
┗━┓ (1.2)
  ┃ ✅ : 9 : ⊤
  ┗ _ : 4 ≺ 5
```
-/
#eval
  Branch.one (.fml ⟨1, (⊤ : NNFormula ℕ)⟩ true) $
  Branch.two (.fml ⟨2, (⊤ : NNFormula ℕ)⟩ true)
    (
      .one (.fml ⟨3, (atom 1) ⋎ (atom 3)⟩ true) $
      .two (.fml ⟨5, (⊤ : NNFormula ℕ)⟩ true)
        (
          .one (.fml ⟨6, (⊤ : NNFormula ℕ)⟩ true) $
          .zero (.rel (1, 2))
        )
        (
          .one (.fml ⟨8, (⊤ : NNFormula ℕ)⟩ true) $
          .zero (.rel (2, 3))
        )
    )
    (
      .one (.fml ⟨9, (⊤ : NNFormula ℕ)⟩ true) $
      .zero (.rel (4, 5))
    )

/-
```
┃.
┣━┓.1
┃ ┣━┓.1.1
┃ ┃ ┣━━.1.1.1
┃ ┃ ┗━━.1.1.2
┃ ┗━┓.1.2
┃   ┣━━.1.2.1
┃   ┗━━.1.2.2
┗━┓.2
  ┣━━.2.1
  ┗━━.2.2
```
-/


abbrev Path := List (LabelledFormula)

namespace Path

def isClosed (P : Path) : Prop := ∃ l φ, (l ∶ φ) ∈ P ∧ (l ∶ ∼φ) ∈ P

instance : DecidablePred Path.isClosed := by
  sorry;

def labels (P : Path) : List Label := P.map LabelledFormula.label
#eval Path.labels [0 ∶ atom 1, 1 ∶ atom 2, 2 ∶ atom 3]

def fresh_label (P : Path) : Label := (P.labels.foldl max 0) + 1
#eval Path.fresh_label [0 ∶ atom 1, 1 ∶ atom 2, 2 ∶ atom 3]

end Path



abbrev NodePath := List Node

namespace NodePath

def formulae : NodePath → List LabelledFormula
  | [] => []
  | (.fml lφ _) :: xs => lφ :: (formulae xs)
  | (.rel _) :: xs => formulae xs

def uncheckedFormulae : NodePath → List LabelledFormula
  | [] => []
  | (.fml lφ false) :: xs => lφ :: (uncheckedFormulae xs)
  | (.fml _ true) :: xs => uncheckedFormulae xs
  | (.rel _) :: xs => uncheckedFormulae xs

def rels : NodePath → List RelTerm
  | [] => []
  | (.fml _ _) :: xs => rels xs
  | (.rel rt) :: xs => rt :: rels xs

def labels : NodePath → List Label
  | [] => []
  | (.fml ⟨l, _⟩ _) :: xs => l :: labels xs
  | (.rel (l₁, l₂)) :: xs => l₁ :: l₂ :: labels xs

def freshLabel (P : NodePath) : Label := (P.labels.foldl max 0) + 1

#eval
  uncheckedFormulae ([
    (.fml (0 ∶ ∼(□((atom 0) ➝ (atom 1)) ➝ (□(atom 0) ➝ □(atom 1)))) true),
    (.fml (0 ∶ ∼(□((atom 0) ➝ (atom 1)) ➝ (□(atom 0) ➝ □(atom 1)))) true)
  ])

end NodePath
-/

namespace Branch

def mature : Branch → Bool
  | .zero (.fml _ b) _ _ => b
  | .zero (.rel _) _ _ => true
  | .one (.fml _ b) _ _ B => b && B.mature
  | .one (.rel _) _ _ B => B.mature
  | .two (.fml _ b) _ _ B₁ B₂ => b && B₁.mature && B₂.mature
  | .two (.rel _) _ _ B₁ B₂ => B₁.mature && B₂.mature

lemma _root_.Nat.noe {n m : ℕ} : n ≤ m → n ≠ m → n < m := by
  omega;

def glow : Branch → Branch
  | .zero (.fml (l ∶ atom a) false) n R => .zero (.fml (l ∶ atom a) true) n R
  | .zero (.fml (l ∶ natom a) false) n R => .zero (.fml (l ∶ natom a) true) n R
  | .zero (.fml (l ∶ φ ⋏ ψ) false) n R =>
      .one (.fml (l ∶ (φ ⋏ ψ)) true) n R $
      .one (.fml (l ∶ φ) false) n R $
      .zero (.fml (l ∶ ψ) false) n R
  | .zero (.fml (l ∶ φ ⋎ ψ) false) n R =>
      .two (.fml (l ∶ (φ ⋎ ψ)) true) n R
      (.zero (.fml (l ∶ φ) false) n R)
      (.zero (.fml (l ∶ ψ) false) n R)
  | .zero (.fml (l ∶ ◇φ) false) n R =>
      .one (.fml (l ∶ ◇φ) true) n R $
      .one (.rel (l, n)) n R $
      .zero (.fml (n ∶ φ) false) (n + 1)
        (λ m =>
          if h : m = n then []
          else
            have := m.2
            letI m : Fin n := ⟨m.1, by sorry⟩
            if m = l then n :: R m
            else R m
        )
  | .zero N n R => .zero N n R
  | .one (.fml (l ∶ atom a) false) n R B => .one (.fml (l ∶ atom a) true) n R B
  | .one (.fml (l ∶ natom a) false) n R B => .one (.fml (l ∶ natom a) true) n R B
  | .one (.fml (l ∶ φ ⋏ ψ) false) n R B =>
      .one (.fml (l ∶ φ ⋏ ψ) true) n R $
      .one (.fml (l ∶ φ) false) n R $
      .one (.fml (l ∶ ψ) false) n R $
      B
  | .one (.fml (l ∶ φ ⋎ ψ) false) n R B =>
      .two (.fml (l ∶ φ ⋎ ψ) true) n R
      (.one (.fml (l ∶ φ) false) n R $ B)
      (.one (.fml (l ∶ ψ) false) n R $ B)
  | .one N n R B => .one N n R (glow B)
  | .two (.fml (l ∶ atom a) false) n R B₁ B₂ => .two (.fml (l ∶ atom a) true) n R B₁ B₂
  | .two (.fml (l ∶ natom a) false) n R B₁ B₂ => .two (.fml (l ∶ natom a) true) n R B₁ B₂
  | .two N n R B₁ B₂ =>
    if B₁.mature
      then .two N n R B₁ (glow B₂)
      else .two N n R (glow B₁) B₂

#eval glow $ glow $ glow $ glow $ glow $ glow $ glow $ glow $ glow $ glow $ glow (
  .one (.fml (1 ∶ (atom 0)) false) $
  .one (.fml (2 ∶ (natom 2)) false) $
  .one (.fml (3 ∶ (natom 3) ⋏ (atom 4) ⋏ (atom 5)) false) $
  .zero (.fml (4 ∶ (atom 6) ⋏ (atom 7)) false)
)

#eval glow $ glow $ glow $ glow $ glow $ glow $ glow $ glow $ glow (
  .zero (.fml (0 ∶ ((atom 2) ⋎ (natom 0)) ⋎ ((atom 1) ⋏ ((atom 2) ⋎ (atom 3)))) false)
)

#eval glow $ glow $ glow $ glow $ glow $ glow $ glow $ glow $ glow $ glow $ glow $ glow $ glow (
  .one (.fml (0 ∶ (natom 0) ⋎ (atom 1)) false) $
  .one (.fml (0 ∶ (natom 0) ➝ (atom 1)) false) $
  .zero (.fml (0 ∶ (atom 0)) false)
)

#eval glow $ glow (
  .zero (.fml (0 ∶ ◇(atom 0)) false)
)

end Branch


namespace Branch

def node_paths : Branch → List NodePath :=
  let rec rc (Ps : List NodePath) : Branch → List NodePath := λ
    | .zero N => Ps.map (λ P => N :: P)
    | .one N P => rc (Ps.map (λ P => N :: P)) P
    | .two N P₁ P₂ => (rc (Ps.map (λ P => N :: P)) P₁) ++ (rc (Ps.map (λ P => N :: P)) P₂)
  rc [[]]

#eval
  (
    Branch.one (.fml (0 ∶ ∼(□((atom 0) ➝ (atom 1)) ➝ (□(atom 0) ➝ □(atom 1)))) true) $
    Branch.one (.fml (0 ∶ □((natom 0) ⋎ (atom 1))) true) $
    Branch.one (.fml (0 ∶ □(atom 0) ⋏ ◇(natom 1)) true) $
    Branch.one (.fml (0 ∶ □(atom 0)) true) $
    Branch.one (.fml (0 ∶ ◇(natom 1)) true) $
    Branch.one (.rel (0, 1)) $
    Branch.one (.fml (1 ∶ natom 1) true) $
    Branch.one (.fml (1 ∶ atom 0) true) $
    Branch.two (.fml (1 ∶ (natom 0) ⋎ (atom 1)) true)
    (
      Branch.zero (.fml (1 ∶ (natom 0)) true))
    (
      Branch.zero (.fml (1 ∶ (atom 1)) true)
    )
  ).node_paths

def paths : Branch → List Path :=
  let rec rc (Ps : List Path) : Branch → List Path := λ
    | .zero N =>
      match N with
      | .fml lφ _ => Ps.map (λ P => lφ :: P)
      | .rel _ => Ps
    | .one N P =>
      match N with
      | .fml lφ _ => rc (Ps.map (λ P => lφ :: P)) P
      | .rel _ => rc Ps P
    | .two N P₁ P₂ =>
      match N with
      | .fml lφ _ => (rc (Ps.map (λ P => lφ :: P)) P₁) ++ (rc (Ps.map (λ P => lφ :: P)) P₂)
      | .rel _ => (rc Ps P₁) ++ (rc Ps P₂)
  rc [[]]

#eval
  (
    Branch.zero (.fml (4 ∶ ((atom 1) ⋏ (atom 3))) true)
  ).paths

#eval
  (
    Branch.one (.fml (1 ∶ ⊤) true) $
    Branch.zero (.fml (4 ∶ ((atom 1) ⋏ (atom 3))) true)
  ).paths

#eval
  (
    Branch.one (.fml ⟨1, (⊤ : NNFormula ℕ)⟩ true) $
    Branch.two (.fml ⟨2, (⊤ : NNFormula ℕ)⟩ true)
      (
        .one (.fml ⟨3, (atom 1) ⋎ (atom 3)⟩ true) $
        .two (.fml ⟨5, (⊤ : NNFormula ℕ)⟩ true)
          (
            .one (.fml ⟨6, (⊤ : NNFormula ℕ)⟩ true) $
            .zero (.rel (1, 2))
          )
          (
            .one (.fml ⟨8, (⊤ : NNFormula ℕ)⟩ true) $
            .zero (.rel (2, 3))
          )
      )
      (
        .one (.fml ⟨9, (⊤ : NNFormula ℕ)⟩ true) $
        .zero (.rel (4, 5))
      )
  ).paths

def isClosed (P : Branch) : Prop := P.paths.any Path.isClosed
instance : DecidablePred Branch.isClosed := by
  sorry

#eval ∼(□((atom 0) ➝ (atom 1)) ➝ (□(atom 0) ➝ □(atom 1)))

#eval
  (
    Branch.one (.fml (0 ∶ ∼(□((atom 0) ➝ (atom 1)) ➝ (□(atom 0) ➝ □(atom 1)))) true) $
    Branch.one (.fml (0 ∶ □((natom 0) ⋎ (atom 1))) true) $
    Branch.one (.fml (0 ∶ □(atom 0) ⋏ ◇(natom 1)) true) $
    Branch.one (.fml (0 ∶ □(atom 0)) true) $
    Branch.one (.fml (0 ∶ ◇(natom 1)) true) $
    Branch.one (.rel (0, 1)) $
    Branch.one (.fml (1 ∶ natom 1) true) $
    Branch.one (.fml (1 ∶ atom 0) true) $
    Branch.two (.fml (1 ∶ (natom 0) ⋎ (atom 1)) true)
    (
      Branch.zero (.fml (1 ∶ (natom 0)) true))
    (
      Branch.zero (.fml (1 ∶ (atom 1)) true)
    )
  ).paths

#eval
  (
    Branch.two (.fml ⟨0, ∼(□((atom 0) ➝ (atom 1)) ➝ (□(atom 0) ➝ □(atom 1)))⟩ false)
      (
        .one (.fml ⟨3, (atom 1) ⋎ (atom 3)⟩ true) $
        .two (.fml ⟨5, (⊤ : NNFormula ℕ)⟩ true)
          (
            .one (.fml ⟨6, (⊤ : NNFormula ℕ)⟩ true) $
            .zero (.rel (1, 2))
          )
          (
            .one (.fml ⟨8, (⊤ : NNFormula ℕ)⟩ true) $
            .zero (.rel (2, 3))
          )
      )
      (
        .two (.fml ⟨0, (◇(natom 0) ⋎ □(atom 1))⟩ true)
        (
          .zero (.fml ⟨0, ◇(natom 0)⟩ true)
        )
        (
          .zero (.fml ⟨0, □(atom 1)⟩ true)
        )
      )
  ).paths

end Branch

/-
structure Path (α β : Type*) where
  nodes : List (LabelledFormula)
  positive : List (ℕ ×)
  negative : List (ℕ ×)

namespace Path

def length (p : Path β) : Nat := p.nodes.length

def get (p : Path β) (i : Fin p.length) : LabelledFormula := p.nodes.get i

section toStr

variable [ToString] [ToString β]

def toStr (p : Path β) : String :=
  letI nodesStr := String.intercalate ", " (p.nodes.map λ φ => s!"{φ}")
  s!"[{nodesStr}] : {p.positive} : {p.negative}"
instance : Repr (Path β) := ⟨λ t _ => toStr t⟩

-- #eval (⟨[⟨0, atom 1 ➝ NNFormula.atom 2⟩, ⟨1, NNFormula.atom 1⟩], [], []⟩ : Path ℕ ℕ)

end toStr


section Rules

open NNFormula

def and (p : Path β) (i : Fin p.length) : Path β :=
  let ⟨l, φ⟩ := p.get i;
  match φ with
  | φ₁ ⋏ φ₂ =>
    match φ₁, φ₂ with
    | (atom a), (atom b) => {
      nodes := p.nodes.eraseIdx i,
      positive := ⟨l, a⟩ :: ⟨l, b⟩ :: p.positive,
      negative := p.negative
    }
    | (atom a), φ₂ => {
      nodes := ⟨l, φ₂⟩ :: p.nodes.eraseIdx i,
      positive := ⟨l, a⟩ :: p.positive,
      negative := p.negative
    }
    | φ₁, (atom b) => {
      nodes := ⟨l, φ₁⟩ :: p.nodes.eraseIdx i,
      positive := ⟨l, b⟩ :: p.positive,
      negative := p.negative
    }
    | (natom a), (natom b) => {
      nodes := p.nodes.eraseIdx i,
      positive := p.positive,
      negative := ⟨l, a⟩ :: ⟨l, b⟩ :: p.negative
    }
    | (natom a), φ₂ => {
      nodes := ⟨l, φ₂⟩ :: p.nodes.eraseIdx i,
      positive := p.positive,
      negative := p.negative ++ [⟨l, a⟩]
    }
    | φ₁, (natom b) => {
      nodes := ⟨l, φ₁⟩ :: p.nodes.eraseIdx i,
      positive := p.positive,
      negative := p.negative ++ [⟨l, b⟩]
    }
    | φ₁, φ₂ => {
      nodes := ⟨l, φ₁⟩ :: ⟨l, φ₂⟩ :: p.nodes.eraseIdx i,
      positive := p.positive,
      negative := p.negative
    }
  | _ => p

def atom (p : Path β) (i : Fin p.length) : Path β :=
  let ⟨l, φ⟩ := p.get i;
  match φ with
  | .atom a =>
    letI pos := ⟨l, a⟩ :: p.positive;
    {
      nodes := p.nodes.eraseIdx i,
      positive := pos,
      negative := p.negative
    }
  | _ => p



/-
#eval
  (⟨[⟨0, NNFormula.atom 1 ⋏ NNFormula.atom 2⟩, ⟨1, NNFormula.atom 1⟩], [], []⟩ : Path ℕ ℕ)
  |>.and (⟨0, by simp [Path.length]⟩)
  -- |>.atom (⟨0, by sorry⟩)

#eval (⟨[⟨0, NNFormula.atom 1 ⋏ NNFormula.atom 2⟩, ⟨1, NNFormula.atom 1⟩], [], []⟩ : Path ℕ ℕ) |>.atom (⟨1, by simp [Path.length]⟩)
-/

end Rules


end Path



structure Step (α β : Type*) where
  paths : List (LabelledFormula)
  positive : List (ℕ ×)
  negative : List (ℕ ×)
  next : List (Step β)

namespace Step

variable [ToString] [ToString β]

def toStr (s : Step β) : String :=
  letI pathsStr := String.intercalate ", " (s.paths.map λ φ => s!"{φ}");
  s!"[{pathsStr}]\npos: {s.positive}\nneg: {s.negative}"
instance : Repr (Step β) := ⟨λ t _ => toStr t⟩
instance : ToString (Step β) := ⟨toStr⟩

end Step

def Step.mkStep (p : Step β) : Step β :=
  match p.paths with
  | [] => ⟨[], p.positive, p.negative, []⟩
  | ⟨l, .atom a⟩ :: as =>
    {
      paths := as,
      positive := ⟨l, a⟩ :: p.positive,
      negative := p.negative,
      next := []
    }
  | ⟨l, .natom a⟩ :: as =>
    {
      paths := as,
      positive := p.positive,
      negative := ⟨l, a⟩ :: p.negative,
      next := []
    }
  | ⟨l, φ₁ ⋏ φ₂⟩ :: as =>
    {
      paths := ⟨l, φ₁⟩ :: ⟨l, φ₂⟩ :: as,
      positive := p.positive,
      negative := p.negative,
      next := []
    }
  | ⟨l, φ⟩ :: as => p

#eval (⟨[0 ∶ atom 1, 1 ∶ atom 2], [], [], []⟩ : Step ℕ ℕ) |>.mkStep |>.mkStep
-/


end Tableau

end LO.Modal
