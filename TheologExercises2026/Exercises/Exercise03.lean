import TheologExercises2026.Exercises.Exercise02

inductive Literal (Atom : Type u) : Type u where
| pos : Atom -> Literal Atom
| neg : Atom -> Literal Atom
deriving BEq

def Clause (Atom : Type u) := List (Literal Atom)

instance [BEq Atom] :  BEq (Clause Atom) := List.instBEq

def Literal.toString {Atom : Type u} [ToString Atom] : Literal Atom -> String
| .pos p => ToString.toString p
| .neg p => s!"¬{ToString.toString p}"

instance [ToString S] : ToString (Literal S) where
  toString := Literal.toString

variable {Atom : Type u}

def Clause.resolve [BEq Atom] : Clause Atom -> Clause Atom -> List (Clause Atom) :=
fun K1 K2 => (K1.map
  (fun l1 => match l1 with
    | .pos p => if K2.contains (.neg p) then (K1.removeAll [l1] ++ K2.removeAll [(.neg p)]) else []
    | .neg p => if K2.contains (.pos p) then (K1.removeAll [l1] ++ K2.removeAll [(.pos p)]) else []
  )).eraseDups.removeAll []


def K1 : Clause Char := [.neg 'p', .pos 'q']
def K2 : Clause Char := [.pos 'p', .neg 'q']
#eval K1.resolve K2

def List.resolve [BEq Atom] : List (Clause Atom) -> List (Clause Atom) := fun 𝓚 =>
  𝓚 ++ ((𝓚.zip 𝓚).map (fun t => t.fst.resolve t.snd)).flatten.eraseDups

def clauses : List (Clause Char) := [[.neg 'a', .pos 'b'], [.neg 'b', .pos 'c'], [.neg 'c', .pos 'd'], [.pos 'a'], [.neg 'd'], [.neg 'e', .pos 'b']]

#eval clauses.resolve
