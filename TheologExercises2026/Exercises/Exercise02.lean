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

def Formula.ite (F G H : Formula Atom) : Formula Atom := ⟪ (F ∧ G) ∨ (¬ F ∧ H) ⟫

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
theorem sheet02_exercise01 (q : Atom) : ∀ F : IteOnlyFormula Atom, ¬ (F.toFormula === .not (.atom q)) := by
  intro F contra
  specialize contra allTrue
  rw [sheet02_exercise01Aux] at contra
  simp [allTrue, Valuation.eval] at contra


-- If we also have top and bottom then we can always express each formula using ite (and top and bot).

inductive IteWithTopAndBotFormula (Atom : Type u) : Type u where
| top : IteWithTopAndBotFormula Atom
| bot : IteWithTopAndBotFormula Atom
| atom : Atom -> IteWithTopAndBotFormula Atom
| ite : IteWithTopAndBotFormula Atom -> IteWithTopAndBotFormula Atom -> IteWithTopAndBotFormula Atom -> IteWithTopAndBotFormula Atom

def IteWithTopAndBotFormula.toFormula [Inhabited Atom] : IteWithTopAndBotFormula Atom -> Formula Atom
| .top => .or (.atom default) (.not (.atom default))
| .bot => .and (.atom default)  (.not (.atom default))
| .atom a => .atom a
| .ite f g h => .ite f.toFormula g.toFormula h.toFormula

def IteWithTopAndBotFormula.fromFormula : Formula Atom -> IteWithTopAndBotFormula Atom
| .empty => .top
| .atom a => .atom a
| .not f => .ite (fromFormula f) .bot .top
| .and f g => .ite (fromFormula f) (fromFormula g) .bot
| .or f g => .ite (fromFormula f) .top (fromFormula g)
| .imp f g => .ite (fromFormula f) (fromFormula g) .top
| .eq f g => .ite (fromFormula f) (fromFormula g) (.ite (fromFormula g) .bot .top)

theorem IteWithTopAndBotFormula.fromFormula_equiv [Inhabited Atom] :
    ∀ F : Formula Atom, (fromFormula F).toFormula === F := by
  intro F
  fun_induction fromFormula with
  | case1 => simp only [toFormula]; intro v; simp [Valuation.eval]
  | case2 a => simpa [toFormula] using Formula.equiv_refl
  | case3 f ih =>
    simp only [toFormula, Formula.ite]
    intro v
    specialize ih v
    grind
  | case4 f g ih_f ih_g =>
    simp only [toFormula, Formula.ite]
    intro v
    specialize ih_f v
    specialize ih_g v
    grind
  | case5 f g ih_f ih_g =>
    simp only [toFormula, Formula.ite]
    intro v
    specialize ih_f v
    specialize ih_g v
    grind
  | case6 f g ih_f ih_g =>
    simp only [toFormula, Formula.ite]
    intro v
    specialize ih_f v
    specialize ih_g v
    grind
  | case7 f g ih_f ih_g =>
    simp only [toFormula, Formula.ite]
    intro v
    specialize ih_f v
    specialize ih_g v
    grind

end Exercise01

section Exercise02

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

inductive NNFFormula (Atom : Type u) : Type u where
| empty : NNFFormula Atom
| atom : Atom -> NNFFormula Atom
| negatom : Atom -> NNFFormula Atom
| and : NNFFormula Atom -> NNFFormula Atom -> NNFFormula Atom
| or : NNFFormula Atom -> NNFFormula Atom -> NNFFormula Atom

def OnlyAndOrNotFormula.toNNF : OnlyAndOrNotFormula Atom -> NNFFormula Atom
| .not (.atom p) => .negatom p
| .and F G => .and F.toNNF G.toNNF
| .or F G => .or F.toNNF G.toNNF
| .not (.not F) => F.toNNF
| .not (.and F G) => .or (OnlyAndOrNotFormula.not F).toNNF (OnlyAndOrNotFormula.not G).toNNF
| .not (.or F G) => .and (OnlyAndOrNotFormula.not F).toNNF (OnlyAndOrNotFormula.not G).toNNF
| .atom p => .atom p
| _ => .empty

def NNFFormula.toFormula : NNFFormula Atom -> Formula Atom
| .empty => .empty
| .atom p => .atom p
| .negatom p => .not (.atom p)
| .or F G => .or F.toFormula G.toFormula
| .and F G => .and F.toFormula G.toFormula

def Formula.depth : Formula Atom -> Nat
| .empty => 0
| .atom _ => 0
| .not F => F.depth + 1
| .and F G => (max F.depth G.depth) + 1
| .or F G => (max F.depth G.depth) + 1
| .imp F G => (max F.depth G.depth) + 1
| .eq F G => (max F.depth G.depth) + 1

#eval ⟪ "p" ∨ ("q" ∧ ¬"r") ⟫.depth

def NNFFormula.and_or_distr : NNFFormula Atom -> NNFFormula Atom
| .and F (.or G H) => .or (.and F G) (.and F H)
| .and (.or F G) H => .or (.and F H) (.and G H)
| F => F

def Formula.and_or_distr : Formula Atom -> Formula Atom
| ⟪ F ∧ (G ∨ H) ⟫ => ⟪ (F ∧ G) ∨ (F ∧ H) ⟫
| ⟪ (F ∨ G) ∧ H ⟫ => ⟪ (F ∧ H) ∨ (G ∧ H) ⟫
| F => F

#eval ⟪ ("p" ∨ ¬"r") ∧ ((¬"q" ∨ "p") ∨ "v") ⟫.and_or_distr

#eval ⟪ ("x" → ("p" → "q") → "r" ) ⟫.to_only_andornot.toFormula
#eval ⟪ ("x" → ("p" → "q") → "r" ) ⟫.to_only_andornot.NNF.toFormula

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

-- Exercise 2a
def F_a := ⟪ ¬("p" ↔ "q") ⟫

#eval F_a.to_only_andornot.NNF.toFormula

def v_a : Valuation String := fun p => match p with
| "p" => true
| "q" => false
| _ => false

theorem a : F_a.satisfiable := by unfold Formula.satisfiable; exists v_a

-- Exercise 2b
def F_b := ⟪ ¬(("p" ∨ "q") ∧ (¬"p" ∨ "r") ∧ (¬"q" ∨ "r")) ⟫

#eval F_b.to_only_andornot.NNF.toFormula

def v_b : Valuation String := fun p => match p with
| "r" => false
| "q" => true
| _ => false

theorem b : F_b.satisfiable := by unfold Formula.satisfiable; exists v_b

end Exercise02
