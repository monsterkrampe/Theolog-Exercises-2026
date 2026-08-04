import TheologExercises2026.Exercises.Exercise02

theorem Formula.de_morgan1 (F G : Formula Atom) : ⟪ ¬(F ∧ G) ⟫ === ⟪ ¬F ∨ ¬G ⟫ := by intro v; grind
theorem Formula.de_morgan2 (F G : Formula Atom) : ⟪ ¬(F ∨ G) ⟫ === ⟪ ¬F ∧ ¬G ⟫ := by intro v; grind

theorem Formula.not_equiv_of_equiv (F G : Formula Atom) : F === G -> F.not === G.not := by
  intro equiv v
  unfold Valuation.eval
  specialize equiv v
  grind

theorem Formula.eq_onlyAndOrNot : ∀ (F : Formula Atom), F === F.to_only_andornot.toFormula := by
  intro F
  unfold equiv
  intro v
  induction F with
  | atom p => simp only [to_only_andornot, OnlyAndOrNotFormula.toFormula]
  | not F => simp only [to_only_andornot, OnlyAndOrNotFormula.toFormula]; grind
  | and F G h1 h2 => simp only [to_only_andornot, OnlyAndOrNotFormula.toFormula]; grind
  | or F G h1 h2 => simp only [to_only_andornot, OnlyAndOrNotFormula.toFormula]; grind
  | imp F G h1 h2 => simp only [to_only_andornot, OnlyAndOrNotFormula.toFormula]; grind
  | eq F G h1 h2 => simp only [to_only_andornot, OnlyAndOrNotFormula.toFormula]; grind
  | _ => simp only [to_only_andornot, OnlyAndOrNotFormula.toFormula]

theorem NNFFormula.DNF_isDNF (F : NNFFormula Atom) : F.DNF.isDNF := by
  induction F with
  | and F1 F2 h1 h2 =>
    unfold isDNF-- DNF DNF.loop
    cases h : (F1.and F2).DNF with
    | and G1 G2 =>
      simp only [Bool.and_eq_true]
      constructor
      . unfold DNF DNF.loop at h

        sorry
      . sorry
    | or G1 G2 =>
      simp only [Bool.and_eq_true]

      sorry
    | _ => grind
  | or F1 F2 h1 h2 =>
    unfold isDNF
    sorry
  | _ => sorry

theorem test (F G : OnlyAndOrNotFormula Atom) : (F.and G).toFormula === (F.and G).toNNF.toFormula -> (F.and G).not.toFormula === (F.and G).not.toNNF.toFormula := by
  intro equiv v
  specialize equiv v
  have aux : v.eval (F.and G).not.toFormula = v.eval (F.and G).toFormula.not := by rfl
  --have aux2 : v.eval (F.and G).not.toNNF.toFormula = v.eval (F.and G).toNNF.toFormula.not := by sorry
  simp only [aux, Valuation.eval]--, equiv]
  apply Classical.byContradiction
  intro contra
  simp at contra

  sorry

theorem Formula.not_eq_not_NNF (F : Formula Atom) : F === F.to_only_andornot.toNNF.toFormula → ⟪ ¬F ⟫ === ⟪ ¬F ⟫.to_only_andornot.toNNF.toFormula := by
  intro equiv v
  induction F with
  | top =>
    simp only [to_only_andornot, OnlyAndOrNotFormula.toNNF]
    unfold Valuation.eval NNFFormula.toFormula
    simp only
    rfl
  | bot =>
    simp only [to_only_andornot, OnlyAndOrNotFormula.toNNF]
    unfold Valuation.eval NNFFormula.toFormula
    simp only
    rfl
  | atom p =>
    simp only [to_only_andornot, OnlyAndOrNotFormula.toNNF]
    rfl
  | and F1 F2 h1 h2 =>
    simp only [to_only_andornot, OnlyAndOrNotFormula.toNNF, Valuation.eval]
    sorry
  | _ =>
    sorry

theorem Formula.eq_NNF (F : Formula Atom) : F === F.to_only_andornot.toNNF.toFormula := by
  unfold equiv
  intro v
  rw [eq_onlyAndOrNot]
  induction F with
  | top => simp only [to_only_andornot, OnlyAndOrNotFormula.toFormula, OnlyAndOrNotFormula.toNNF]; rfl
  | bot => simp only [to_only_andornot, OnlyAndOrNotFormula.toFormula, OnlyAndOrNotFormula.toNNF]; rfl
  | atom p => simp only [to_only_andornot, OnlyAndOrNotFormula.toFormula, OnlyAndOrNotFormula.toNNF]; rfl
  | not F h =>
    simp only [to_only_andornot, OnlyAndOrNotFormula.toFormula, Valuation.eval, Bool.not_eq_eq_eq_not, h]

    sorry
  | and F G h1 h2 =>
    simp only [to_only_andornot, OnlyAndOrNotFormula.toFormula, OnlyAndOrNotFormula.toNNF, Valuation.eval, h1, h2]
    rfl
  | or F G h1 h2 =>
    simp only [to_only_andornot, OnlyAndOrNotFormula.toFormula, OnlyAndOrNotFormula.toNNF, Valuation.eval, h1, h2]
    rfl
  | imp F G h1 h2 =>
    simp only [to_only_andornot, OnlyAndOrNotFormula.toFormula, OnlyAndOrNotFormula.toNNF]--, Valuation.eval, h1, h2]

    sorry
  | eq F G h1 h2 =>
    simp only [to_only_andornot, OnlyAndOrNotFormula.toFormula, OnlyAndOrNotFormula.toNNF, Valuation.eval, h1, h2]

    sorry

theorem OnlyAndOrNotFormula.eq_NNF' (F : OnlyAndOrNotFormula Atom) : F.toFormula === F.toNNF.toFormula := by
  unfold Formula.equiv
  intro v
  induction F with
  | top =>
    simp only [toFormula, toNNF, NNFFormula.toFormula]
  | bot => simp only [toFormula, toNNF, NNFFormula.toFormula]
  | atom => simp only [toFormula, toNNF, NNFFormula.toFormula]
  | and => simp only [toFormula, toNNF, NNFFormula.toFormula, Valuation.eval]; grind
  | or => simp only [toFormula, toNNF, NNFFormula.toFormula, Valuation.eval]; grind
  | not G ih =>
    --simp only [toFormula, Valuation.eval]
    induction hG : G with
    | top => sorry
    | bot => sorry
    | atom => sorry
    | and G1 G2 h1 h2 =>
      simp only [toNNF, toFormula]
      rw [Formula.de_morgan1]
      rw [hG] at ih
      have aux : (G1.not.and G2.not).toNNF = G1.not.toNNF.and G2.not.toNNF := by
        conv =>
          lhs
          unfold toNNF

      sorry
    | _ =>
      sorry

theorem Formula.eq_DNF (F : Formula Atom) : F === F.to_only_andornot.toNNF.DNF.toFormula := by sorry

namespace NNFFormula

def atoms : NNFFormula Atom -> List Atom
| .atom p => [p]
| .negatom p => [p]
| .or F G => F.atoms ++ G.atoms
| .and F G => F.atoms ++ G.atoms
| _ => []

def new_atom (F : NNFFormula Nat) : Nat := match F.atoms with
| [] => 0
| a::l => (a::l).max (by grind) + 1

end NNFFormula

