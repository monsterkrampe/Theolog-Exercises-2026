inductive Formula (Atom : Type u) : Type u where
| atom : Atom -> Formula Atom
| not : Formula Atom -> Formula Atom
| and : Formula Atom -> Formula Atom -> Formula Atom
| or : Formula Atom -> Formula Atom -> Formula Atom
| imp : Formula Atom -> Formula Atom -> Formula Atom
| eq : Formula Atom -> Formula Atom -> Formula Atom
deriving Repr

def exampleFormula : Formula Char := .and (.atom 'P') (.not (.atom 'Q'))

namespace Formula

variable {Atom : Type u}

-- In the lecture this is a set. We consider a list of subformulae here to avoid introducing a set definition. 
-- Opposed to the set, the list might have duplicates but this should not matter much for our considerations.
def subformulae (f : Formula Atom) : List (Formula Atom) := match f with 
  | .atom _ => [f]
  | .not g => f :: g.subformulae
  | .and g h => f :: g.subformulae ++ h.subformulae
  | .or g h => f :: g.subformulae ++ h.subformulae
  | .imp g h => f :: g.subformulae ++ h.subformulae
  | .eq g h => f :: g.subformulae ++ h.subformulae

#eval exampleFormula.subformulae

end Formula

def Valuation (Atom : Type u) := Atom -> Bool

def allTrue : Valuation Char := fun _ => true
def allFalse : Valuation Char := fun _ => false
def onlyPTrue : Valuation Char := fun c => c = 'P'

namespace Valuation

variable {Atom : Type u}

def eval (v : Valuation Atom) : Formula Atom -> Bool 
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

