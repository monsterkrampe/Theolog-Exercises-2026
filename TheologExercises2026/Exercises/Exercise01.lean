inductive Formula (Atom : Type u) : Type u where
| empty : Formula Atom
| atom : Atom -> Formula Atom
| not : Formula Atom -> Formula Atom
| and : Formula Atom -> Formula Atom -> Formula Atom
| or : Formula Atom -> Formula Atom -> Formula Atom
| imp : Formula Atom -> Formula Atom -> Formula Atom
| eq : Formula Atom -> Formula Atom -> Formula Atom

def Formula.toString {Atom : Type u} [ToString Atom] : Formula Atom -> String
| .empty => "⊤"
| .atom a => ToString.toString a
| .not f => s!"p¬ {toString f}"
| .and f g => s!"({toString f} p∧ {toString g})"
| .or f g => s!"({toString f} p∨ {toString g})"
| .imp f g => s!"({toString f} p-> {toString g})"
| .eq f g => s!"({toString f} p↔ {toString g})"

instance [ToString S] : ToString (Formula S) where
  toString := Formula.toString

prefix:60 "p¬ " => Formula.not
infixl:50 " p∧ " => Formula.and
infixl:50 " p∨ " => Formula.or
infixl:50 " p-> " => Formula.imp
infixl:50 " p↔  " => Formula.eq


section ExampleDefinitions

def P := Formula.atom 'P'
def Q := Formula.atom 'Q'

def exampleFormula : Formula Char := P p∧ (p¬ Q)

end ExampleDefinitions


section FromLecture

namespace Formula

variable {Atom : Type u}

-- In the lecture this is a set. We consider a list of subformulae here to avoid introducing a set definition. 
-- Opposed to the set, the list might have duplicates but this should not matter much for our considerations.
def subformulae (f : Formula Atom) : List (Formula Atom) := match f with 
  | .empty => []
  | .atom _ => [f]
  | .not g => f :: g.subformulae
  | .and g h => f :: g.subformulae ++ h.subformulae
  | .or g h => f :: g.subformulae ++ h.subformulae
  | .imp g h => f :: g.subformulae ++ h.subformulae
  | .eq g h => f :: g.subformulae ++ h.subformulae

#eval exampleFormula.subformulae

end Formula

def Valuation (Atom : Type u) := Atom -> Bool

def allTrue {Atom : Type u} : Valuation Atom := fun _ => true
def allFalse {Atom : Type u} : Valuation Atom := fun _ => false
def onlyPTrue : Valuation Char := fun c => c = 'P'

namespace Valuation

variable {Atom : Type u}

@[grind]
def eval (v : Valuation Atom) : Formula Atom -> Bool 
| .empty => true
| .atom a => v a
| .not f => !v.eval f
| .and f g => v.eval f && v.eval g
| .or f g => v.eval f || v.eval g
| .imp f g => v.eval f -> v.eval g
| .eq f g => v.eval f ↔ v.eval g

#eval allTrue.eval exampleFormula
#eval allFalse.eval exampleFormula
#eval onlyPTrue.eval exampleFormula

end Valuation

end FromLecture


section Exercise01

def exA := Formula.atom 'a'
def exB := Formula.atom 'b'
def exC := Formula.atom 'c'
def exD := Formula.atom 'd'
def Ex01Formula := p¬ ((exD p↔ exB) p∧ (exC p-> (exD p∨ p¬ exA)))

#eval Ex01Formula.subformulae

end Exercise01


section Exercise02

variable {Atom : Type u}

namespace Formula

def entails (f g : Formula Atom) : Prop := ∀ v : Valuation Atom, v.eval f -> v.eval g
infix:50 " ⊧ " => entails

def list_entails (l : List (Formula Atom)) (f : Formula Atom) : Prop := ∀ v : Valuation Atom, l.all v.eval -> v.eval f
infix:50 " ⊧ " => list_entails

def list_to_formula : List (Formula Atom) -> Formula Atom 
| [] => .empty
| [f] => f
| hd::tl => hd p∧ (list_to_formula tl)

/- 
The following two theorems are currently not required for anything (not even the grinds in exercise02X). 
We just want to prove that list_to_formula and list_entails behave as expected.
-/

@[simp, grind =]
theorem eval_list_to_formula {v : Valuation Atom} {l : List (Formula Atom)} : v.eval (list_to_formula l) = l.all v.eval := by 
  fun_induction list_to_formula <;> grind

@[simp, grind =]
theorem list_entails_iff {l : List (Formula Atom)} {f : Formula Atom} : l ⊧ f ↔ ((list_to_formula l) ⊧ f) := by 
  unfold entails list_entails; grind

end Formula

-- First holds.
theorem sheet01_exercise02A : ∀ {a b c : Formula Atom}, [p¬ a p∨ b, p¬ b p∨ c, b p∧ c] ⊧ ((a p↔ b) p∨ c) := by 
  intro a b c
  intro v
  grind

-- Second holds.
theorem sheet01_exercise02B : ∀ {a b c : Formula Atom}, [a p-> b, c p∨ a, a p-> p¬ b, p¬ c] ⊧ a := by 
  intro a b c
  intro v
  grind

-- Third holds.
theorem sheet01_exercise02C : ∀ {a b c : Formula Atom}, [(a p∧ p¬ b) p∨ (p¬ a p∧ b), p¬ c p∧ b, p¬ (p¬ a p∨ b)] ⊧ (p¬ (a p∨ b)) := by 
  intro a b c
  intro v
  grind

-- This one does not hold.
theorem nonEntailmentExample : ¬ [exA p∧ exB, exB p-> p¬ exC] ⊧ exC := by 
  unfold exA exB exC
  intro contra
  let v := fun atom => match atom with 
    | 'a' => true
    | 'b' => true
    | 'c' => false
    | _ => false
  specialize contra v
  grind

end Exercise02


section Exercise03

variable {Atom : Type u}

namespace Formula

def satisfiable (f : Formula Atom) : Prop := ∃ (v : Valuation Atom), v.eval f 

def unsatisfiable (f : Formula Atom) : Prop := ¬ f.satisfiable

def tautologie (f : Formula Atom) : Prop := ∀ (v : Valuation Atom), v.eval f

end Formula

theorem sheet01_exercise03A : ∀ {p : Formula Atom}, (p¬ p¬ p p↔ p).satisfiable := by 
  intro p
  exists allTrue 
  grind

theorem sheet01_exercise03B : ∀ {p q : Formula Atom}, (p¬ p p∧ ((p p∨ q) p∧ p¬ q)).unsatisfiable := by 
  intro p q
  intro ⟨v, contra⟩
  grind

theorem sheet01_exercise03C : ∀ {p q r : Formula Atom}, (((p p∧ q) p-> r) p↔ (p p-> (q p-> r))).tautologie := by 
  intro p q r
  intro v
  grind

end Exercise03


section Exercise04

variable {Atom : Type u}

namespace Formula

def size : Formula Atom -> Nat 
| .empty => 0
| .atom _ => 1
| .not f => f.size + 1
| .and f g => f.size + g.size + 1
| .or f g => f.size + g.size + 1
| .imp f g => f.size + g.size + 1
| .eq f g => f.size + g.size + 1

#print exampleFormula

#eval exampleFormula.size

def atoms : Formula Atom -> List Atom
| .empty => []
| .atom a => [a]
| .not f => f.atoms
| .and f g => f.atoms ++ g.atoms
| .or f g => f.atoms ++ g.atoms
| .imp f g => f.atoms ++ g.atoms
| .eq f g => f.atoms ++ g.atoms

#eval exampleFormula.atoms

theorem atom_sublist_subformulae {f : Formula Atom} : List.Sublist (f.atoms.map .atom) f.subformulae := by 
  induction f with 
  | empty => simp [atoms]
  | atom _ => simp [atoms, subformulae]
  | not f ih => simp only [atoms, subformulae]; grind
  | and f g ih_f ih_g => simp only [atoms, subformulae]; grind
  | or f g ih_f ih_g => simp only [atoms, subformulae]; grind
  | imp f g ih_f ih_g => simp only [atoms, subformulae]; grind
  | eq f g ih_f ih_g => simp only [atoms, subformulae]; grind

end Formula

theorem sheet01_exercise04B {f : Formula Atom} : f.subformulae.length ≤ f.size := by 
  induction f with 
  | empty => simp [Formula.subformulae, Formula.size]
  | atom _ => simp [Formula.subformulae, Formula.size]
  | not f ih => simpa [Formula.subformulae, Formula.size] using ih
  | and f g ih_f ih_g => simp only [Formula.subformulae, Formula.size]; grind
  | or f g ih_f ih_g => simp only [Formula.subformulae, Formula.size]; grind
  | imp f g ih_f ih_g => simp only [Formula.subformulae, Formula.size]; grind
  | eq f g ih_f ih_g => simp only [Formula.subformulae, Formula.size]; grind

-- Note that this depends on exercise04B
theorem sheet01_exercise04A {f : Formula Atom} : f.atoms.length <= f.size := by 
  suffices (f.atoms.map Formula.atom).length ≤ f.subformulae.length by apply Nat.le_trans _ sheet01_exercise04B; grind
  apply List.Sublist.length_le
  exact Formula.atom_sublist_subformulae

end Exercise04


section Exercise05

def VL := Formula.atom "VL" -- Lucy is vampire.
def VM := Formula.atom "VM" -- Minna is vampire.
def CL := Formula.atom "CL" -- Lucy is cracy.
def CM := Formula.atom "CM" -- Minna is crazy.

def v : Valuation String := fun s => match s with 
  | "VL" => true -- Lucy is the vampire.
  | "VM" => false -- Minna is not the vampire.
  | "CL" => true -- Lucy is crazy.
  | "CM" => true -- Minna is crazy.
  | _ => false

def oneVamp := VL p↔ p¬ VM
def statementLucy := (VL p↔ CL) p↔ (CL p∧ CM)
def statementMinna := (VM p↔ CM) p↔ p¬ (CL p∧ CM)

#eval [oneVamp, statementLucy, statementMinna].all v.eval

theorem sheet01_exercise05 : [oneVamp, statementLucy, statementMinna].all v.eval := by decide

end Exercise05

