import TheologExercises2026.Exercises.Exercise01

section Prelims 

variable {Atom : Type u}

namespace Formula

def equiv (f g : Formula Atom) : Prop := ∀ v : Valuation Atom, v.eval f = v.eval g
infix:50 " === " => equiv

theorem equiv_refl {f : Formula Atom} : f === f := by intro _; rfl

theorem equiv_symm {f g : Formula Atom} : f === g -> g === f := by intro h v; rw [h v]

theorem equiv_trans {f g h : Formula Atom} : f === g -> g === h -> f === h := by intro eq1 eq2 v; rw [eq1 v, eq2 v]

theorem equiv_iff_entails_both_ways {f g : Formula Atom} : f === g ↔ (f ⊧ g ∧ g ⊧ f) := by 
  constructor
  . intro equiv; constructor
    . intro v; rw [equiv v]; simp
    . intro v; rw [equiv v]; simp
  . intro ⟨entails1, entails2⟩ v
    rw [Bool.eq_iff_iff]
    constructor
    . exact entails1 v
    . exact entails2 v

end Formula

end Prelims

section Exercise01

variable {Atom : Type u}

def Formula.ite (F G H : Formula Atom) : Formula Atom := (F p∧ G) p∨ (p¬ F p∧ H)

inductive IteOnlyFormula (Atom : Type u) : Type u where
| atom : Atom -> IteOnlyFormula Atom
| ite : IteOnlyFormula Atom -> IteOnlyFormula Atom -> IteOnlyFormula Atom -> IteOnlyFormula Atom

def IteOnlyFormula.toFormula : IteOnlyFormula Atom -> Formula Atom 
| .atom a => .atom a
| .ite f g h => .ite f.toFormula g.toFormula h.toFormula

/--
This is not required but an interesting insight about ite. If both consequences are equivalent, 
then the ite is equivalent to this consequence.
-/
theorem Formula.ite_equiv_arg_of_args_equiv {f g h : Formula Atom} : g === h -> f.ite g h === g := by 
  intro eq v
  simp only [ite, Valuation.eval]
  rw [eq v]
  cases v.eval f <;> simp

/-- Every IteOnlyFormula is true under the valuation that maps each atom to true. -/
theorem sheet02_exercise01Aux : ∀ F : IteOnlyFormula Atom, allTrue.eval F.toFormula := by 
  intro F
  fun_induction IteOnlyFormula.toFormula with 
  | case1 a => simp [allTrue, Valuation.eval]
  | case2 f g h ih_f ih_g ih_h => simp [Valuation.eval, Formula.ite, ih_f, ih_g, ih_h]

/-- For p¬ q with an atom q we cannot find an equivalent IteOnlyFormula. -/
theorem sheet02_exercise01 (q : Atom) : ∀ F : IteOnlyFormula Atom, ¬ (F.toFormula === p¬ (.atom q)) := by 
  intro F contra
  specialize contra allTrue
  rw [sheet02_exercise01Aux] at contra
  simp [allTrue, Valuation.eval] at contra

end Exercise01

