import TheologExercises2026.Exercises.Exercise01

variable {Atom : Type u}

theorem list_entails_iff_unsat (L : List (Formula Atom)) (F : Formula Atom) : L ⊧ F ↔ Formula.unsatisfiable (Formula.list_to_formula ((.not F)::L)) := by
  rw [Formula.list_entails_iff]
  unfold Formula.entails Formula.unsatisfiable Formula.satisfiable
  constructor
  . intro h contra
    grind
  . intro h v v_eval
    simp only [Formula.eval_list_to_formula, not_exists] at h
    grind

instance Formula.instDecidableEq [DecidableEq Atom] : DecidableEq (Formula Atom)
| .empty, F => by
  cases F with
  | empty => apply isTrue; rfl
  | _ F => apply isFalse; grind
| .atom p, F => by
  cases F with
  | atom q =>
    by_cases hp : p = q
    . apply isTrue; rw [hp]
    . apply isFalse; grind
  | empty => apply isFalse; grind
  | _ F => apply isFalse; grind
| .not F, G => by
  cases G with
  | not H =>
    have aux : p¬ F = p¬ H ↔ F = H := by grind
    rw [aux]
    apply instDecidableEq
  | _ => apply isFalse; grind
| .and F G, H => by
  cases H with
  | and H1 H2 =>
    have aux : (F p∧ G) = (H1 p∧ H2) ↔ (F = H1) ∧ (G = H2) := by grind
    rw [aux]
    have test := instDecidableEq F H1
    have test2 := instDecidableEq G H2
    have aux2 := instDecidableAnd (p := F = H1) (q := G = H2)
    exact aux2
  | _ => apply isFalse; grind
| .or F G, H => by
  cases H with
  | or H1 H2 =>
    have aux : (F p∨ G) = (H1 p∨ H2) ↔ (F = H1) ∧ (G = H2) := by grind
    rw [aux]
    have test := instDecidableEq F H1
    have test2 := instDecidableEq G H2
    have aux2 := instDecidableAnd (p := F = H1) (q := G = H2)
    exact aux2
  | _ => apply isFalse; grind
| .imp F G, H => by
  cases H with
  | imp H1 H2 =>
    have aux : (F p-> G) = (H1 p-> H2) ↔ (F = H1) ∧ (G = H2) := by grind
    rw [aux]
    have test := instDecidableEq F H1
    have test2 := instDecidableEq G H2
    have aux2 := instDecidableAnd (p := F = H1) (q := G = H2)
    exact aux2
  | _ => apply isFalse; grind
| .eq F G, H => by
  cases H with
  | eq H1 H2 =>
    have aux : (F p↔ G) = (H1 p↔ H2) ↔ (F = H1) ∧ (G = H2) := by grind
    rw [aux]
    have test := instDecidableEq F H1
    have test2 := instDecidableEq G H2
    have aux2 := instDecidableAnd (p := F = H1) (q := G = H2)
    exact aux2
  | _ => apply isFalse; grind

instance [DecidableEq Atom] : LawfulBEq (Formula Atom) := inferInstance
instance [DecidableEq Atom] : BEq (Formula Atom) := inferInstance

def Formula.has_subformula : Formula Atom -> Formula Atom -> Prop :=
fun F G => G ∈ F.subformulae

instance [DecidableEq Atom] (F G : Formula Atom) : Decidable (F.has_subformula G) := by
  have aux : F.has_subformula G ↔ G ∈ F.subformulae := by
      constructor
      . unfold Formula.has_subformula; simp only [imp_self]
      . unfold Formula.has_subformula; simp only [imp_self]
  rw [aux]
  have inst := List.instDecidableMemOfLawfulBEq (α := Formula Atom) G F.subformulae
  exact inst

def Formula.replace_first [DecidableEq Atom] : Formula Atom -> Formula Atom -> Formula Atom -> Formula Atom
| .atom p => fun F G =>
    match F with
    | .atom q => if p ≠ q then .atom p else G
    | _ => .atom p
| .empty => fun _ _ => .empty
| .not H => fun F G =>
    if F = H then .not G else H.replace_first F G
| .and F1 F2 => fun G H =>
    if F1 = G then .and H F2 else
    if F1.has_subformula G then .and (F1.replace_first G H) F2
    else .and F1 (F2.replace_first G H)
| .or F1 F2 => fun G H =>
    if F1 = G then .or H F2 else
    if F1.has_subformula G then .or (F1.replace_first G H) F2
    else .or F1 (F2.replace_first G H)
| .imp F1 F2 => fun G H =>
    if F1 = G then .imp H F2 else
    if F1.has_subformula G then .imp (F1.replace_first G H) F2
    else .imp F1 (F2.replace_first G H)
| .eq F1 F2 => fun G H =>
    if F1 = G then .eq H F2 else
    if F1.has_subformula G then .eq (F1.replace_first G H) F2
    else .eq F1 (F2.replace_first G H)

variable {p q r v : Atom} [DecidableEq Atom]

def F1 : Formula String := ⟪ "H" ∧ "G" ↔ "K" ∧ ¬"H" ⟫

#eval F1.replace_first ⟪ "H" ⟫ ⟪ "T" ⟫

inductive OnlyAndOrNotFormula (Atom : Type u) : Type u where
| atom : Atom -> OnlyAndOrNotFormula Atom
| and : OnlyAndOrNotFormula Atom -> OnlyAndOrNotFormula Atom -> OnlyAndOrNotFormula Atom
| or : OnlyAndOrNotFormula Atom -> OnlyAndOrNotFormula Atom -> OnlyAndOrNotFormula Atom
| not : OnlyAndOrNotFormula Atom -> OnlyAndOrNotFormula Atom

def Formula.to_only_andornot : Formula Atom -> OnlyAndOrNotFormula Atom
| .atom p => .atom p
| .empty => sorry
| .not F => .not F.to_only_andornot
| .imp F G => .or (.not F.to_only_andornot) G.to_only_andornot
| .eq F G => .or (.and F.to_only_andornot G.to_only_andornot) (.and (.not F.to_only_andornot) (.not G.to_only_andornot))
| .and F G => .and F.to_only_andornot G.to_only_andornot
| .or F G => .or F.to_only_andornot G.to_only_andornot

def OnlyAndOrNotFormula.toFormula : OnlyAndOrNotFormula Atom -> Formula Atom
| .atom p => .atom p
| .and F G => .and F.toFormula G.toFormula
| .or F G => .or F.toFormula G.toFormula
| .not F => .not F.toFormula

def Formula.only_andornot : Formula Atom -> Prop
| .atom _ => True
| .empty => True
| .not F => F.only_andornot
| .and F G => F.only_andornot ∧ G.only_andornot
| .or F G => F.only_andornot ∧ G.only_andornot
| .imp F G => F.only_andornot ∧ G.only_andornot
| .eq F G => F.only_andornot ∧ G.only_andornot

def OnlyAndOrNotFormula.NNF : OnlyAndOrNotFormula Atom -> OnlyAndOrNotFormula Atom
| .atom p => .atom p
| .and F G => .and F.NNF G.NNF
| .or F G => .or F.NNF G.NNF
| .not (.not F) => F.NNF
| .not (.atom p) => .not (.atom p)
| .not (.and F G) => .or (OnlyAndOrNotFormula.not F).NNF (OnlyAndOrNotFormula.not G).NNF
| .not (.or F G) => .and (OnlyAndOrNotFormula.not F).NNF (OnlyAndOrNotFormula.not G).NNF
