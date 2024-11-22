import Foundation.Modal.NNFormula

namespace LO.Modal

open NNFormula

namespace Tableau


structure LabelledFormula where
  label : ℕ
  formula : NNFormula ℕ

namespace LabelledFormula

notation:max l " ∶ " φ => LabelledFormula.mk l φ

section toStr

def toStr (lf : LabelledFormula) : String := s!"{lf.label} : {lf.formula.toStr}"

instance : Repr (LabelledFormula) := ⟨λ t _ => toStr t⟩
instance : ToString (LabelledFormula) := ⟨toStr⟩

#eval (0 ∶ (atom 1 ➝ atom 2))

end toStr


section deq

def deq (lf₁ lf₂ : LabelledFormula) : Bool := lf₁.formula = lf₂.formula
instance : BEq LabelledFormula := ⟨deq⟩

end deq


end LabelledFormula



abbrev RelTerm := ℕ × ℕ

namespace RelTerm

notation a " ≺ " b => (a, b)

section toStr

def toStr (rt : RelTerm) : String := s!"{rt.1} ≺ {rt.2}"
instance : Repr RelTerm := ⟨λ t _ => toStr t⟩
instance : ToString RelTerm := ⟨toStr⟩

end toStr

end RelTerm



abbrev RelTerms := List RelTerm

namespace RelTerms

abbrev rel (rs : RelTerms) := rs.contains

end RelTerms


structure GenFormula where
  formula : LabelledFormula
  generated : List LabelledFormula
deriving Repr, BEq


structure Path where
  path : List GenFormula
  rels : List (ℕ × ℕ)
deriving Repr

namespace Path

section toStr

-- def toStr (P : Path) : String := P.map (λ ⟨lφ, g⟩ => s!"{lφ} => {g}\n") |> String.join

-- instance : Repr Path := ⟨λ t _ => toStr t⟩

#eval (⟨[
    ⟨(0 ∶ atom 1), []⟩,
    ⟨(0 ∶ atom 1 ⋏ atom 2), []⟩
  ], []⟩ : Path)

def insert_gf (gf : GenFormula) : Path → Path := λ ⟨path, rels⟩ => ⟨path.insert gf, rels⟩

end toStr

partial def applyRules₁ : Path → List (Path) := λ ⟨nodes, rels⟩ =>
  match nodes with
  | [] => [⟨[], rels⟩]
  | ⟨l ∶ atom p, []⟩ :: rest =>
    applyRules₁ ⟨rest, rels⟩ |>.map $ insert_gf ⟨l ∶ atom p, [l ∶ atom p]⟩
  | ⟨l ∶ natom p, []⟩ :: rest =>
    applyRules₁ ⟨rest, rels⟩ |>.map $ insert_gf ⟨l ∶ natom p, [l ∶ natom p]⟩
  | ⟨l ∶ φ ⋏ ψ, []⟩ :: rest =>
    applyRules₁ (⟨rest |>.insert ⟨l ∶ ψ, []⟩ |>.insert ⟨l ∶ φ, []⟩, rels⟩) |>.map $ insert_gf ⟨l ∶ φ ⋏ ψ, [l ∶ φ, l ∶ ψ]⟩
  | ⟨l ∶ φ ⋎ ψ, []⟩ :: rest =>
    (applyRules₁ ⟨rest.insert ⟨l ∶ φ, []⟩, rels⟩ |>.map $ insert_gf ⟨l ∶ φ ⋎ ψ, [l ∶ φ]⟩)
    ++
    (applyRules₁ ⟨rest.insert ⟨l ∶ ψ, []⟩, rels⟩ |>.map $ insert_gf ⟨l ∶ φ ⋎ ψ, [l ∶ ψ]⟩)
  | ⟨l ∶ ◇φ, []⟩ :: rest =>
    letI m := (l :: rest.map (λ ⟨⟨l, _⟩, _⟩ => l) ++ (rels.map (λ ⟨x, y⟩ => [x, y]) |>.flatten) |>.foldl max 0) + 1
    applyRules₁ ⟨rest.insert ⟨m ∶ φ, []⟩, rels.insert (l, m)⟩ |>.map $ insert_gf ⟨l ∶ ◇φ, [m ∶ φ]⟩
  | gφ :: rest =>
    applyRules₁ ⟨rest, rels⟩ |>.map $ insert_gf gφ

#eval applyRules₁ ⟨[
    ⟨0 ∶ ∼(□(atom 0 ➝ atom 1) ➝ □(atom 0) ➝ □(atom 1)), []⟩,
  ], []⟩

#eval applyRules₁ ⟨[
    ⟨0 ∶ natom 1 ⋏ (atom 2 ⋏ atom 3), []⟩,
    ⟨0 ∶ atom 4 ⋏ atom 5, []⟩,
    ⟨0 ∶ atom 1, []⟩,
  ], []⟩


#eval applyRules₁ ⟨[
    ⟨0 ∶ atom 1 ⋎ (atom 2 ⋏ atom 3), []⟩,
    ⟨0 ∶ atom 4 ⋏ atom 5, []⟩,
    ⟨0 ∶ atom 1, []⟩,
  ], []⟩

#eval applyRules₁ ⟨[
    ⟨0 ∶ ◇(atom 0 ⋏ natom 1), []⟩,
  ], []⟩

#eval applyRules₁ ⟨[
    ⟨0 ∶ ◇(atom 1), []⟩,
    ⟨1 ∶ ◇(atom 0 ⋏ ◇(natom 1)), []⟩,
    ⟨2 ∶ ◇(atom 2), []⟩,
  ], []⟩

#eval (applyRules₁ ⟨[
    ⟨0 ∶ ◇◇◇(atom 1 ⋏ □(atom 2)), []⟩,
    ⟨0 ∶ ◇◇◇(atom 3 ⋏ □(atom 4)), []⟩,
  ], []⟩)


partial def applyRules₂ : Path → Path := λ ⟨nodes, rels⟩ =>
  match nodes with
  | [] => ⟨[], rels⟩
  | ⟨l ∶ □φ, c⟩ :: rest =>
    letI tos : List LabelledFormula := rels
      |>.filter (λ ⟨f, _⟩ => f = l)
      |>.map (λ ⟨_, t⟩ => t ∶ φ)
      |>.filter (!c.contains ·)
    let ges : List GenFormula := tos.map (λ t => ⟨t, []⟩)
    applyRules₂ (⟨rest ++ ges, rels⟩) |>.insert_gf ⟨l ∶ □φ, c ++ tos⟩
    -- Path.insert_gf ⟨l ∶ □φ, c ++ tos⟩ (⟨rest ++ ps, rels⟩)
  | gφ :: rest =>
    applyRules₂ ⟨rest, rels⟩ |>.insert_gf gφ

#eval (applyRules₂ ⟨[
    ⟨0 ∶ □(atom 1 ⋏ □(atom 2)), []⟩,
  ], [(0, 1), (0, 2)]⟩)

#eval (applyRules₂ ⟨[
    ⟨0 ∶ □(atom 1 ⋏ □(atom 2)), []⟩,
  ], [(0, 1), (0, 2), (0, 3), (2, 0)]⟩)

#eval (applyRules₁ $ applyRules₂ ⟨[
    ⟨0 ∶ □(atom 1 ⋏ □(natom 2)), []⟩,
  ], [(0, 1), (0, 2), (0, 3), (2, 0)]⟩) |>.map applyRules₂

#eval (applyRules₂ ⟨[
    ⟨0 ∶ □(atom 0), []⟩,
    ⟨2 ∶ □(atom 1 ⋏ □(natom 2)), []⟩,
  ], [(2, 0), (0, 2), (0, 1)]⟩)

#eval (applyRules₁ $ (applyRules₂ ⟨[
    ⟨0 ∶ □(atom 0), []⟩,
    ⟨2 ∶ □(atom 1 ⋏ □(natom 2)), []⟩,
  ], [(2, 0), (0, 2), (0, 1)]⟩)) |>.map applyRules₂

#eval (⟨[
    ⟨0 ∶ ∼(□(atom 0 ➝ atom 1) ➝ □(atom 0) ➝ □(atom 1)), []⟩,
  ], []⟩ : Path) |>.applyRules₁ |>.map applyRules₂ |> (List.map applyRules₁)

abbrev applyRules := List.flatten ∘ (List.map (applyRules₁ ∘ applyRules₂))


#eval applyRules $ applyRules $ applyRules $ applyRules [(⟨[
    ⟨0 ∶ ∼(□(atom 0 ➝ atom 1) ➝ □(atom 0) ➝ □(atom 1)), []⟩,
  ], []⟩ : Path)]


def isClosed (P : Path) : Bool :=
  let lφs := P.path.map (λ ⟨lφ, _⟩ => lφ)
  lφs.any (λ ⟨l, φ⟩ => lφs.contains ⟨l, ∼φ⟩)

#eval applyRules [(⟨[⟨0 ∶ ∼(□(atom 0 ➝ atom 1) ➝ □(atom 0) ➝ □(atom 1)), []⟩], []⟩ : Path)]
    |>.map (λ P => P.isClosed)

end Path



end Tableau

end LO.Modal
