import TheologExercises2026.Exercises.Exercise03

def HornFormula (Atom : Type u) := List (HornClause Atom)

instance [BEq Atom] (H : HornFormula Atom) : Decidable (H = []) := List.instDecidableEqNil H

instance [BEq Atom] : BEq (HornClause Atom) where
beq := fun C1 C2 => C1.head == C2.head && C1.body == C2.body

instance [BEq Atom] : BEq (HornFormula Atom) where
beq := fun H1 H2 => List.beq H1 H2

variable {Atom : Type u}

def Formula.conjunction_from_list : List (Formula Atom) -> Formula Atom
| .nil => .top
| .cons hd tl => match tl with
  | .nil => hd
  | .cons hd' tl => .and hd (conjunction_from_list (hd'::tl))

namespace HornFormula

def toFormula (H : HornFormula Atom) : Formula Atom :=
  Formula.list_to_formula (H.map (fun C => C.toFormula))

theorem eval_toFormula_eq (H : HornFormula Atom) (v : Valuation Atom) : v.eval H.toFormula = (H.map (·.toFormula)).all v.eval := by
  unfold toFormula
  simp

instance : Membership (HornClause Atom) (HornFormula Atom) := List.instMembership

theorem unsat_iff_contains_empty [BEq Atom] (H : HornFormula Atom) : HornClause.empty ∈ H -> H.toFormula.unsatisfiable := by
  intro empty_mem
  unfold Formula.unsatisfiable
  intro contra
  unfold Formula.satisfiable at contra
  rcases contra with ⟨v, v_eval⟩
  induction H with
  | nil => contradiction
  | cons C H' ih =>
    rw [eval_toFormula_eq] at v_eval
    have aux : ∀ C', C' ∈ C::H' -> v.eval C'.toFormula = true := by grind
    have eval_empty : v.eval HornClause.empty.toFormula = true := aux HornClause.empty empty_mem
    contradiction

end HornFormula
