import TheologExercises2026.Exercises.Exercise03

def HornFormula (Atom : Type u) := List (HornClause Atom)

instance [BEq Atom] (H : HornFormula Atom) : Decidable (H = []) := List.instDecidableEqNil H

instance [BEq Atom] : BEq (HornClause Atom) where
beq := fun C1 C2 => C1.head == C2.head && C1.body == C2.body

instance [BEq Atom] [LawfulBEq Atom] : LawfulBEq (HornClause Atom) where
rfl := by
  intro C
  unfold BEq.beq instBEqHornClause
  simp only [BEq.rfl, Bool.and_self]
eq_of_beq := by
  intro C1 C2 beq
  unfold BEq.beq instBEqHornClause at beq
  simp at beq
  rcases beq with ⟨x,y⟩

  sorry

instance [BEq Atom] : BEq (HornFormula Atom) where
beq := fun H1 H2 => List.beq H1 H2

variable {Atom : Type u}

theorem List.removeAll_not_mem [BEq α] [LawfulBEq α] (l : List α) (a : α) (not_mem : a ∉ l) : l.removeAll [a] = l := by
  unfold removeAll
  simp only [elem_eq_contains, contains_cons, elem_nil, Bool.or_false, filter_eq_self, Bool.not_eq_eq_eq_not, Bool.not_true]
  intro b b_mem
  grind

theorem Formula.disj_from_list_true_iff (L : List (Formula Atom)) (v : Valuation Atom) : v.eval (disjunction_from_list L) ↔ ∃ F, F ∈ L ∧ v.eval F := by
  induction hL : L generalizing L with
  | nil =>
    simp only [List.not_mem_nil, false_and, exists_false, iff_false, Bool.not_eq_true]
    rfl
  | cons F L' ih =>
    simp only [List.mem_cons, exists_eq_or_imp]
    constructor
    . intro h
      cases hF : v.eval F
      . simp only [Bool.false_eq_true, false_or]
        have L_eval : v.eval (disjunction_from_list L') := by unfold disjunction_from_list at h; grind
        exact (ih L' rfl).mp L_eval
      . apply Or.inl; rfl
    . intro h
      rcases h with inl | inr
      . unfold disjunction_from_list; grind
      . rcases inr with ⟨G, G_mem, G_eval⟩
        unfold disjunction_from_list; grind

namespace HornClause

theorem eval_true_iff [BEq Atom] [LawfulBEq Atom] (C : HornClause Atom) (v : Valuation Atom) : v.eval C.toFormula = true ↔ ∃ p, (C.head.isEqSome p ∧ v.eval (.atom p) = true) ∨ (p ∈ C.body ∧ v.eval (.atom p) = false) := by
  by_cases h : C.head = none ∨ ∃ p, C.head.isEqSome p ∧ !v.eval (Formula.atom p)
  . constructor
    . intro eval
      cases hC : C.head with
      | none =>
        simp only [Option.isEqSome_eq_beq_some, Option.none_beq_some, Bool.false_eq_true, false_and, false_or]
        unfold toFormula at eval
        simp only [hC, Formula.disj_from_list_true_iff] at eval
        rcases eval with ⟨l, l_mem, l_eval⟩
        grind
      | some p =>
        simp only [hC, reduceCtorEq, Option.isEqSome_eq_beq_some, Option.some_beq_some, beq_iff_eq,
          Bool.not_eq_eq_eq_not, Bool.not_true, exists_eq_left', false_or] at h
        unfold toFormula at eval
        simp [hC, Formula.disj_from_list_true_iff] at eval
        rcases eval with inl | inr
        . grind
        . rcases inr with ⟨l, l_mem, l_eval⟩
          grind
    . intro h_exists
      rcases h_exists with ⟨p, hp⟩
      rcases hp with inl | inr
      . grind
      . unfold toFormula
        rcases h with inl' | inr'
        . simp [inl']
          have aux : ∃ F, F ∈ List.map (fun a => (Formula.atom a).not) C.body ∧ v.eval F = true := by
            exists (Formula.atom p).not
            grind
          exact (Formula.disj_from_list_true_iff (C.body.map (fun a => (Formula.atom a).not)) v).mpr aux
        . rcases inr' with ⟨q, q_eq, q_eval⟩
          simp only [Option.isEqSome_eq_beq_some, beq_iff_eq] at q_eq
          simp only [q_eq]
          have aux : ∃ F, F ∈ (Formula.atom q)::(C.body.map (fun a => (Formula.atom a).not)) ∧ v.eval F = true := by
            exists (Formula.atom p).not
            grind
          exact (Formula.disj_from_list_true_iff ((Formula.atom q)::(C.body.map (fun a => (Formula.atom a).not))) v).mpr aux
  . simp only [Option.isEqSome_eq_beq_some, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true, not_or, not_exists, not_and, Bool.not_eq_false] at h
    rcases h with ⟨hd_eq, eval⟩
    rw [← ne_eq, ← Option.isSome_iff_ne_none, Option.isSome_iff_exists] at hd_eq
    rcases hd_eq with ⟨p, hd_eq⟩
    constructor
    . intro h
      exists p
      apply Or.inl
      grind
    . intro h
      unfold toFormula Formula.disjunction_from_list
      simp only [hd_eq]
      grind


def remove [BEq Atom] (C : HornClause Atom) (p : Atom) : HornClause Atom :=
mk (if C.head.isEqSome p then none else C.head) (C.body.removeAll [p])

def atoms [BEq Atom] (C : HornClause Atom) : List Atom := match C.head, C.body with
| none, C' => C'.eraseDups
| some p, C' => p::C'.eraseDups

def is_unit_clause (C : HornClause Atom) : Bool := match C.head, C.body with
| none, [_] => true
| some _, [] => true
| _, _ => false

def toString [ToString Atom] (C : HornClause Atom) : String := match C.head with
| none => "{" ++ (C.body.foldl (· ++ "¬" ++ ToString.toString · ++ ", ") "") ++ "}"
| some p => "{" ++ ToString.toString p ++ ", " ++ C.body.foldl (· ++ "¬" ++ ToString.toString · ++ ", ") "" ++ "}"

instance [ToString S] : ToString (HornClause S) where
  toString := HornClause.toString

end HornClause

namespace HornFormula

def toFormula (H : HornFormula Atom) : Formula Atom :=
  Formula.list_to_formula (H.map (fun C => C.toFormula))

def atoms [BEq Atom] (H : HornFormula Atom ) : List Atom :=
  (H.map (fun C => C.atoms)).flatten

theorem eval_toFormula_eq (H : HornFormula Atom) (v : Valuation Atom) : v.eval H.toFormula = (H.map (·.toFormula)).all v.eval := by
  unfold toFormula
  simp

instance : Membership (HornClause Atom) (HornFormula Atom) := List.instMembership
instance [BEq Atom] [LawfulBEq (HornClause Atom)] {C : HornClause Atom} {H : HornFormula Atom} : Decidable (C ∈ H) := List.instDecidableMemOfLawfulBEq C H

theorem unsat_if_contains_empty [BEq Atom] (H : HornFormula Atom) : HornClause.empty ∈ H -> H.toFormula.unsatisfiable := by
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

def unit [BEq Atom] [LawfulBEq (HornClause Atom)] (L : HornClause Atom) (H : HornFormula Atom) : HornFormula Atom :=
if L ∈ H then match L.head, L.body with
| none, [p] => (H.filter (fun C => !(C.body.elem p))).map (fun C => C.remove p)
| some p, [] => (H.filter (fun C => !(C.head.isEqSome p))).map (fun C => C.remove p)
| _, _ => H
else H

theorem unit_le [BEq Atom] [LawfulBEq (HornClause Atom)] (L : HornClause Atom) (H : HornFormula Atom) : (H.unit L).length ≤ H.length := by unfold unit; grind

theorem unit_lt [BEq Atom] [ReflBEq Atom] [LawfulBEq Atom] [LawfulBEq (HornClause Atom)] (L : HornClause Atom) (H : HornFormula Atom) : L.is_unit_clause -> L ∈ H -> (H.unit L).length < H.length := by
  unfold HornClause.is_unit_clause unit
  simp only [List.elem_eq_contains, Option.isEqSome_eq_beq_some]
  intro is_unit mem
  simp only [mem]
  split at is_unit
  next p hd_eq b_eq =>
    have L_eq : L = HornClause.mk none [p] := by rw [← hd_eq, ← b_eq]
    simp only [if_true, List.length_map, List.length_filter_lt_length_iff_exists]
    exists HornClause.mk none [p]
    rw [← L_eq]
    constructor
    . exact mem
    . grind
  next hd tl p hd_eq tl_eq =>
    simp only [if_true, List.length_map, List.length_filter_lt_length_iff_exists, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_eq_false]
    exists L
    constructor
    . exact mem
    . grind
  next x y z => contradiction

theorem sat_iff_unit_sat [BEq Atom] [LawfulBEq Atom] [LawfulBEq (HornClause Atom)] (H : HornFormula Atom) (L : HornClause Atom) : H.toFormula.satisfiable ↔ (H.unit L).toFormula.satisfiable := by
  unfold Formula.satisfiable
  constructor
  . intro sat
    rcases sat with ⟨v, v_sat⟩
    exists v
    unfold unit
    rw [eval_toFormula_eq] at *
    by_cases L_mem : L ∈ H
    . simp only [L_mem, if_true]
      . split
        next hd body p hd_eq body_eq =>
          simp?
          intro C C_mem
          by_cases hC : C.body.contains p
          . apply Or.inl; grind
          . apply Or.inr
            have C_eval : v.eval C.toFormula = true := by grind
            simp at hC
            rw [HornClause.eval_true_iff] at C_eval
            have test := (HornClause.eval_true_iff (C.remove p) v).mpr
            rcases C_eval with ⟨q, hq⟩
            have aux : ∃ q, (C.remove p).head.isEqSome q = true ∧ v.eval (Formula.atom q) = true ∨ q ∈ (C.remove p).body ∧ v.eval (Formula.atom q) = false := by
              exists q

              sorry


            --rcases C_eval with ⟨q, ⟨q_hd, q_eval⟩ | ⟨q_mem, q_eval⟩⟩

            sorry
        next hd body p hd_eq body_eq =>
          simp
          intro C C_mem
          by_cases hC : C.head == some p
          . apply Or.inl; grind
          . apply Or.inr
            simp only [Bool.not_eq_true] at hC
            have C_eval : v.eval C.toFormula = true := by grind
            unfold HornClause.remove
            simp only [Option.isEqSome_eq_beq_some, hC, Bool.false_eq_true, ↓reduceIte]
            by_cases p_mem : p ∈ C.body
            . have aux' : L.toFormula = (Formula.atom p) := by
                unfold HornClause.toFormula Formula.disjunction_from_list
                simp only [hd_eq, body_eq, List.map_nil]
              have aux : v.eval (Formula.atom p) := by grind

              sorry
            . have body_eq : C.body.removeAll [p] = C.body := by apply List.removeAll_not_mem; exact p_mem
              have aux : { head := C.head, body := C.body.removeAll [p] } = C := by rw [body_eq]
              rw [aux]; exact C_eval
        . grind
    . simp only [L_mem, if_false]; grind

  sorry

def unit_clauses : HornFormula Atom -> List (HornClause Atom)
| [] => []
| C::H' => if C.is_unit_clause then C::(unit_clauses H') else unit_clauses H'

theorem unit_clauses_sub {H : HornFormula Atom} : H.unit_clauses ⊆ H := by
  induction H <;> (unfold unit_clauses; grind)

theorem is_unit_clause_of_mem_unit_clauses {C : HornClause Atom} {H : HornFormula Atom} : C ∈ H.unit_clauses -> C.is_unit_clause := by
  induction H <;> (unfold unit_clauses; grind)

def unit_propagation [BEq Atom] [LawfulBEq Atom] (H : HornFormula Atom) : HornFormula Atom :=
  match eq : H.unit_clauses with
  | [] => H
  | C::_ =>
    have _termination : (H.unit C).length < H.length := by
      suffices C ∈ H.unit_clauses by
        apply unit_lt -- NOTE: this requires LawfulBEq Atom; I did not check why
        . exact is_unit_clause_of_mem_unit_clauses this
        . exact unit_clauses_sub this
      simp [eq]
    unit_propagation (H.unit C)
termination_by H.length

end HornFormula


def K : HornFormula String := [{head := some "b", body := [] : HornClause String}, {head := some "c", body := ["b"] : HornClause String}, {head := some "d", body := ["c"] : HornClause String}, {head := none, body := ["d"] : HornClause String}, {head := some "b", body := ["e"] : HornClause String}]
def K' : HornFormula String := [{head := some "p", body := [] : HornClause String}, {head := none, body := ["q", "p"] : HornClause String}]

#eval! HornFormula.unit_propagation K'
#eval! HornFormula.unit_propagation K
