import TheologExercises2026.Exercises.Exercise01
import TheologExercises2026.Exercises.Exercise02

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

variable {p q r v : Atom}

def F1 : Formula String := ⟪ "H" ∧ "G" ↔ "K" ∧ ¬"H" ⟫

#eval F1.replace_first ⟪ "H" ⟫ ⟪ "T" ⟫

theorem Formula.ersetzungstheorem  [DecidableEq Atom] (F G G' : Formula Atom) (h_eq : G === G') : F.replace_first G G' === F := by
  induction F with
  | empty =>
    unfold replace_first; apply equiv_refl
  | atom p =>
    unfold replace_first
    cases G with
    | atom r =>
      simp only [ne_eq, ite_not]
      unfold equiv at *
      intro v
      by_cases h : p = r
      . simp only [h, ↓reduceIte]
        specialize h_eq v; symm; exact h_eq
      . simp only [h, ite_false]
    | _ => simp only; apply equiv_refl
  | and F1 F2 h1 h2 =>
    unfold replace_first
    by_cases h : F1 = G
    . simp only [h, ite_true]
      unfold equiv at *
      intro v
      specialize h_eq v
      grind
    . simp only [h, ite_false]
      sorry
  | _ =>
  sorry

inductive OnlyAndOrNotFormula (Atom : Type u) : Type u where
| empty : OnlyAndOrNotFormula Atom
| atom : Atom -> OnlyAndOrNotFormula Atom
| and : OnlyAndOrNotFormula Atom -> OnlyAndOrNotFormula Atom -> OnlyAndOrNotFormula Atom
| or : OnlyAndOrNotFormula Atom -> OnlyAndOrNotFormula Atom -> OnlyAndOrNotFormula Atom
| not : OnlyAndOrNotFormula Atom -> OnlyAndOrNotFormula Atom

def Formula.to_only_andornot : Formula Atom -> OnlyAndOrNotFormula Atom
| .atom p => .atom p
| .empty => .empty
| .not F => .not F.to_only_andornot
| .imp F G => .or (.not F.to_only_andornot) G.to_only_andornot
| .eq F G => .or (.and F.to_only_andornot G.to_only_andornot) (.and (.not F.to_only_andornot) (.not G.to_only_andornot))
| .and F G => .and F.to_only_andornot G.to_only_andornot
| .or F G => .or F.to_only_andornot G.to_only_andornot

def OnlyAndOrNotFormula.toFormula : OnlyAndOrNotFormula Atom -> Formula Atom
| .empty => .empty
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
| .empty => .empty
| .atom p => .atom p
| .and F G => .and F.NNF G.NNF
| .or F G => .or F.NNF G.NNF
| .not empty => .not empty
| .not (.not F) => F.NNF
| .not (.atom p) => .not (.atom p)
| .not (.and F G) => .or (OnlyAndOrNotFormula.not F).NNF (OnlyAndOrNotFormula.not G).NNF
| .not (.or F G) => .and (OnlyAndOrNotFormula.not F).NNF (OnlyAndOrNotFormula.not G).NNF

#eval ⟪ "p" ↔ "q" ⟫.to_only_andornot.toFormula

theorem Formula.eq_onlyAndOrNot : ∀ (F : Formula Atom), F === F.to_only_andornot.toFormula := by
  intro F
  unfold equiv
  intro v
  induction F with
  | empty => simp only [to_only_andornot, OnlyAndOrNotFormula.toFormula]
  | atom p => simp only [to_only_andornot, OnlyAndOrNotFormula.toFormula]
  | not F => simp only [to_only_andornot, OnlyAndOrNotFormula.toFormula]; grind
  | and F G h1 h2 => simp only [to_only_andornot, OnlyAndOrNotFormula.toFormula]; grind
  | or F G h1 h2 => simp only [to_only_andornot, OnlyAndOrNotFormula.toFormula]; grind
  | imp F G h1 h2 => simp only [to_only_andornot, OnlyAndOrNotFormula.toFormula]; grind
  | eq F G h1 h2 => simp only [to_only_andornot, OnlyAndOrNotFormula.toFormula]; grind

/-
c) b∧(a∨b) ∧(¬b∨c) ∧(¬b∨¬c) ∧(¬a∨c)
d)¬ c→ (¬a∧b∧c) ∨(a∧¬b)
-/
