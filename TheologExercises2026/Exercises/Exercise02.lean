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
| .top => .top
| .bot => .bot
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
  | case2 => simp only [toFormula]; intro v; simp [Valuation.eval] --simpa [toFormula] using Formula.equiv_refl
  | case3 p =>
    simpa [toFormula] using Formula.equiv_refl
  | case4 f ih =>
    simp only [toFormula, Formula.ite]
    intro v
    specialize ih v
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
  | case8 f g ih_f ih_g =>
    simp only [toFormula, Formula.ite]
    intro v
    specialize ih_f v
    specialize ih_g v
    grind

end Exercise01


inductive OnlyAndOrNotFormula (Atom : Type u) : Type u where
| top : OnlyAndOrNotFormula Atom
| bot : OnlyAndOrNotFormula Atom
| atom : Atom -> OnlyAndOrNotFormula Atom
| and : OnlyAndOrNotFormula Atom -> OnlyAndOrNotFormula Atom -> OnlyAndOrNotFormula Atom
| or : OnlyAndOrNotFormula Atom -> OnlyAndOrNotFormula Atom -> OnlyAndOrNotFormula Atom
| not : OnlyAndOrNotFormula Atom -> OnlyAndOrNotFormula Atom

def Formula.to_only_andornot : Formula Atom -> OnlyAndOrNotFormula Atom
| .atom p => .atom p
| .top => .top
| .bot => .bot
| .not F => .not F.to_only_andornot
| .imp F G => .or (.not F.to_only_andornot) G.to_only_andornot
| .eq F G => .or (.and F.to_only_andornot G.to_only_andornot) (.and (.not F.to_only_andornot) (.not G.to_only_andornot))
| .and F G => .and F.to_only_andornot G.to_only_andornot
| .or F G => .or F.to_only_andornot G.to_only_andornot

def OnlyAndOrNotFormula.toFormula : OnlyAndOrNotFormula Atom -> Formula Atom
| .top => .top
| .bot => .bot
| .atom p => .atom p
| .and F G => .and F.toFormula G.toFormula
| .or F G => .or F.toFormula G.toFormula
| .not F => .not F.toFormula

inductive NNFFormula (Atom : Type u) : Type u where
| top : NNFFormula Atom
| bot : NNFFormula Atom
| atom : Atom -> NNFFormula Atom
| negatom : Atom -> NNFFormula Atom
| and : NNFFormula Atom -> NNFFormula Atom -> NNFFormula Atom
| or : NNFFormula Atom -> NNFFormula Atom -> NNFFormula Atom
deriving BEq

def OnlyAndOrNotFormula.toNNF : OnlyAndOrNotFormula Atom -> NNFFormula Atom
| .not (.atom p) => .negatom p
| .and F G => .and F.toNNF G.toNNF
| .or F G => .or F.toNNF G.toNNF
| .not (.not F) => F.toNNF
| .not (.and F G) => .or (OnlyAndOrNotFormula.not F).toNNF (OnlyAndOrNotFormula.not G).toNNF
| .not (.or F G) => .and (OnlyAndOrNotFormula.not F).toNNF (OnlyAndOrNotFormula.not G).toNNF
| .atom p => .atom p
| .top => .top
| .bot => .bot
| .not (.top) => .bot
| .not (.bot) => .top

def NNFFormula.toFormula : NNFFormula Atom -> Formula Atom
| .top => .top
| .bot => .bot
| .atom p => .atom p
| .negatom p => .not (.atom p)
| .or F G => .or F.toFormula G.toFormula
| .and F G => .and F.toFormula G.toFormula

def Formula.depth : Formula Atom -> Nat
| .atom _ => 0
| .not F => F.depth + 1
| .and F G => (max F.depth G.depth) + 1
| .or F G => (max F.depth G.depth) + 1
| .imp F G => (max F.depth G.depth) + 1
| .eq F G => (max F.depth G.depth) + 1
| _ => 0

#eval ⟪ "p" ∨ ("q" ∧ ¬"r") ⟫.depth

def NNFFormula.and_or_distr : NNFFormula Atom -> NNFFormula Atom
| .and F (.or G H) => .or (.and F G) (.and F H)
| .and (.or F G) H => .or (.and F H) (.and G H)
| F => F

def NNFFormula.or_and_distr : NNFFormula Atom -> NNFFormula Atom
| .or F (.and G H) => .and (.or F G) (.or F H)
| .or (.and F G) H => .and (.or F H) (.or G H)
| F => F

def Formula.and_or_distr : Formula Atom -> Formula Atom
| ⟪ F ∧ (G ∨ H) ⟫ => ⟪ (F ∧ G) ∨ (F ∧ H) ⟫
| ⟪ (F ∨ G) ∧ H ⟫ => ⟪ (F ∧ H) ∨ (G ∧ H) ⟫
| F => F

def NNFFormula.onlyAnd : NNFFormula Atom -> Bool
| .or _ _ => false
| .and F G => F.onlyAnd && G.onlyAnd
| _ => true

def NNFFormula.onlyOr : NNFFormula Atom -> Bool
| .and _ _ => false
| .or F G => F.onlyOr && G.onlyOr
| _ => true

def NNFFormula.isDNF : NNFFormula Atom -> Bool
| .or F G => F.isDNF && G.isDNF
| .and F G => F.onlyAnd && G.onlyAnd
| _ => true

def NNFFormula.isKNF : NNFFormula Atom -> Bool
| .and F G => F.isKNF && G.isKNF
| .or F G => F.onlyOr && G.onlyOr
| _ => true

def NNFFormula.or_and_distr_rec : NNFFormula Atom -> NNFFormula Atom
| .or F (.and G H) => .and (.or F.or_and_distr_rec G.or_and_distr_rec) (.or F.or_and_distr_rec H.or_and_distr_rec)
| .or (.and F G) H => .and (.or F.or_and_distr_rec H) (.or G.or_and_distr_rec H.or_and_distr_rec)
| .and F G => .and F.or_and_distr_rec G.or_and_distr_rec
| .or (.or F G) H => .or (NNFFormula.or F G).or_and_distr_rec H.or_and_distr_rec
| .or F (.or G H) => .or F.or_and_distr_rec (NNFFormula.or G H).or_and_distr_rec
| F => F

def NNFFormula.and_or_distr_rec : NNFFormula Atom -> NNFFormula Atom
| .and F (.or G H) => .or (.and F.and_or_distr_rec G.and_or_distr_rec) (.and F.and_or_distr_rec H.and_or_distr_rec)
| .and (.or F G) H => .or (.and F.and_or_distr_rec H) (.and G.and_or_distr_rec H.and_or_distr_rec)
| .or F G => .or F.and_or_distr_rec G.and_or_distr_rec
| .and (.and F G) H => .and (NNFFormula.and F G).and_or_distr_rec H.and_or_distr_rec
| .and F (.and G H) => .and F.and_or_distr_rec (NNFFormula.and G H).and_or_distr_rec
| F => F

def NNFFormula.DNF (G : NNFFormula Atom) : NNFFormula Atom :=
let rec loop : Nat -> NNFFormula Atom -> NNFFormula Atom
  | 0, F => F.and_or_distr_rec
  | n+1, F => if F.isDNF then loop 0 F else loop n F.and_or_distr_rec
loop (2^G.toFormula.atoms.length) G


def NNFFormula.KNF (F : NNFFormula Atom) : NNFFormula Atom :=
(Formula.not (F.DNF).toFormula).to_only_andornot.toNNF

theorem NNFFormula.DNF_and (G H : NNFFormula Atom) : (NNFFormula.and G H).isDNF ↔ G.onlyAnd ∧ H.onlyAnd := by
  unfold isDNF; grind

def F := ⟪ (¬("p" ∨ "q") ∧ (("r" ∨ (¬"q" ∨ "p"))) ∧ "p") ⟫
def G := ⟪ "p" ∧ ("q" ∧ (¬"q" ∨ "p")) ⟫

#eval F.to_only_andornot.toNNF.DNF.toFormula
#eval F.to_only_andornot.toNNF.DNF.isDNF
#eval F.to_only_andornot.toNNF.KNF.toFormula
#eval F.to_only_andornot.toNNF.KNF.isKNF
#eval F.to_only_andornot.toNNF.KNF.isDNF

#eval ⟪ ("p" ∨ ¬"r") ∧ ((¬"q" ∨ "p") ∨ "v") ⟫.and_or_distr

#eval ⟪ ("x" → ("p" → "q") → "r" ) ⟫.to_only_andornot.toFormula
#eval ⟪ ("x" → ("p" → "q") → "r" ) ⟫.to_only_andornot.toNNF.toFormula

section Exercise02

-- Exercise 2a
def F_a := ⟪ ¬("p" ↔ "q") ⟫

#eval ⟪ (¬F_a) ⟫.to_only_andornot.toNNF.toFormula

def v_a : Valuation String := fun p => match p with
| "p" => true
| "q" => false
| _ => false

theorem a : F_a.satisfiable := by unfold Formula.satisfiable; exists v_a

-- Exercise 2b
def F_b := ⟪ ¬(("p" ∨ "q") ∧ (¬"p" ∨ "r") ∧ (¬"q" ∨ "r")) ⟫

#eval F_b.to_only_andornot.toNNF.toFormula

def v_b : Valuation String := fun p => match p with
| "r" => false
| "q" => true
| _ => false

theorem b : F_b.satisfiable := by unfold Formula.satisfiable; exists v_b

-- Exercise 2c
def F_c := ⟪ "b" ∧ ("a" ∨ "b") ∧ (¬"b" ∨ "c") ∧ (¬"b" ∨ ¬"c") ∧ (¬"a" ∨ "c") ⟫

#eval F_c.to_only_andornot.toNNF.KNF.toFormula -- hilfe 0_o
#eval F_c.to_only_andornot.toNNF.isKNF

theorem c : F_c.unsatisfiable := by
  unfold Formula.unsatisfiable
  intro contra
  unfold Formula.satisfiable F_c Valuation.eval at contra
  grind

-- Exercise 2d
def F_d := ⟪ ¬("c" → ((¬"a" ∧ "b" ∧ "c") ∨ ("a" ∧ ¬"b"))) ⟫

#eval F_d.to_only_andornot.toNNF.DNF.toFormula

end Exercise02

