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


section Exercise04B

structure HornClause (Atom : Type u) where
  head : Option Atom
  body : List Atom

-- TODO: translation into regular clausest

variable {Atom : Type u}

namespace Valuation

@[grind]
def intersect (v1 v2 : Valuation Atom) : Valuation Atom := fun a => v1 a && v2 a

end Valuation

def Formula.disjunction_from_list : List (Formula Atom) -> Formula Atom
| .nil => .bot
| .cons hd tl =>
  match tl with
  | .nil => hd
  | .cons hd2 tl =>
    .or hd (disjunction_from_list (hd2 :: tl))

namespace HornClause

def toFormula (hc : HornClause Atom) : Formula Atom :=
  match hc.head with
  | .none => Formula.disjunction_from_list (hc.body.map (fun a => .not (.atom a)))
  | .some head => Formula.disjunction_from_list ((.atom head) :: hc.body.map (fun a => .not (.atom a)))

theorem eval_true_for_intersection_of_both_true {hc : HornClause Atom} {v1 v2 : Valuation Atom}
    (v1_true : v1.eval hc.toFormula) (v2_true : v2.eval hc.toFormula) :
    (v1.intersect v2).eval hc.toFormula := by
  induction eq : hc.body generalizing hc with
  | nil =>
    cases head_eq : hc.head with
    | none =>
      simp only [toFormula, head_eq, eq, List.map_nil, Formula.disjunction_from_list] at v1_true
      grind
    | some head =>
      have hc_eq : hc.toFormula = .atom head := by simp only [toFormula, head_eq, eq, List.map_nil, Formula.disjunction_from_list]
      grind
  | cons hd tl ih =>
    simp only [toFormula] at *
    specialize ih (hc := {head := hc.head, body := tl})
    cases tl <;> grind [Formula.disjunction_from_list]

end HornClause

theorem sheet03_exercise04_h1 : ∀ hc : HornClause String, ¬ hc.toFormula.equiv ⟪ "p" ∨ "q" ⟫ := by
  intro hc contra
  let v1 : Valuation String := fun a => match a with
    | "p" => true
    | "q" => false
    | _ => true
  let v2 : Valuation String := fun a => match a with
    | "p" => false
    | "q" => true
    | _ => true
  cases eval_v1 : v1.eval hc.toFormula
  . specialize contra v1; grind
  cases eval_v2 : v2.eval hc.toFormula
  . specialize contra v2; grind
  specialize contra (v1.intersect v2)
  rw [HornClause.eval_true_for_intersection_of_both_true eval_v1 eval_v2] at contra
  grind

theorem sheet03_exercise04_h2 : {head := none, body := ["p", "q"] : HornClause String}.toFormula.equiv ⟪ ¬ ("p" ∧ "q") ⟫ := by
  intro v
  grind [HornClause.toFormula, Formula.disjunction_from_list]

theorem sheet03_exercise04_h3 : ∀ hc : HornClause String, ¬ hc.toFormula.equiv ⟪ "p" ↔ ¬"q" ⟫ := by
  -- same proof as sheet03_exercise04_h1
  intro hc contra
  let v1 : Valuation String := fun a => match a with
    | "p" => true
    | "q" => false
    | _ => true
  let v2 : Valuation String := fun a => match a with
    | "p" => false
    | "q" => true
    | _ => true
  cases eval_v1 : v1.eval hc.toFormula
  . specialize contra v1; grind
  cases eval_v2 : v2.eval hc.toFormula
  . specialize contra v2; grind
  specialize contra (v1.intersect v2)
  rw [HornClause.eval_true_for_intersection_of_both_true eval_v1 eval_v2] at contra
  grind

end Exercise04B
