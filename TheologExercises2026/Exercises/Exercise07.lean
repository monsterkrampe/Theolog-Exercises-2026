import TheologExercises2026.Exercises.Exercise04

variable {Atom : Type u}

namespace Formula

def replace_atom_top [DecidableEq Atom] (F : Formula Atom) (p : Atom) : Formula Atom := match F with
| atom q => if p = q then .top else .atom q
| not G => G.replace_atom_top p
| and G1 G2 => .and (G1.replace_atom_top p) (G2.replace_atom_top p)
| or G1 G2 => .or (G1.replace_atom_top p) (G2.replace_atom_top p)
| imp G1 G2 => .imp (G1.replace_atom_top p) (G2.replace_atom_top p)
| eq G1 G2 => .eq (G1.replace_atom_top p) (G2.replace_atom_top p)
| _ => F

def replace_atom_bot [DecidableEq Atom] (F : Formula Atom) (p : Atom) : Formula Atom := match F with
| atom q => if p = q then .bot else .atom q
| not G => G.replace_atom_bot p
| and G1 G2 => .and (G1.replace_atom_bot p) (G2.replace_atom_bot p)
| or G1 G2 => .or (G1.replace_atom_bot p) (G2.replace_atom_bot p)
| imp G1 G2 => .imp (G1.replace_atom_bot p) (G2.replace_atom_bot p)
| eq G1 G2 => .eq (G1.replace_atom_bot p) (G2.replace_atom_bot p)
| _ => F

def atom_free : Formula Atom -> Prop
| atom _ => False
| and F G => F.atom_free ∧ G.atom_free
| or F G => F.atom_free ∧ G.atom_free
| imp F G => F.atom_free ∧ G.atom_free
| eq F G => F.atom_free ∧ G.atom_free
| not F => F.atom_free
| _ => True

def eval_atom_free (F : Formula Atom) : Bool := match F with
| atom _ => false -- TODO : vielleicht anders machen...
| top => true
| bot => false
| not F => !F.eval_atom_free
| and F G => F.eval_atom_free && G.eval_atom_free
| or F G => F.eval_atom_free || G.eval_atom_free
| imp F G => !F.eval_atom_free || G.eval_atom_free
| eq F G => F.eval_atom_free == G.eval_atom_free

end Formula

inductive Quantor
| _exists
| _forall
notation:70 "∃" => Quantor._exists
notation:70 "∀" => Quantor._forall

def TrueQBF [DecidableEq Atom] (l : List (Quantor × Atom)) (F : Formula Atom) : Bool := match l with
| [] => F.eval_atom_free
| t::l' => match t.fst with
  | ∃ => TrueQBF l' (F.replace_atom_bot (t.snd)) || TrueQBF l' (F.replace_atom_top (t.snd))
  | ∀ => TrueQBF l' (F.replace_atom_bot (t.snd)) && TrueQBF l' (F.replace_atom_top (t.snd))

#eval TrueQBF [(∃, "p1")] ⟪ "p1" ⟫
#eval TrueQBF [(∀, "p1")] ⟪ "p1" ⟫
#eval TrueQBF [(∃, "p1")] ⟪ "⊥" ⟫
#eval TrueQBF [(∀, "p1"), (∃, "p2")] ⟪ "p2" → "p1" ⟫
#eval TrueQBF [(∀, "p1"), (∃, "p2"), (∀, "p3")] ⟪ ("p1" ∨ "p2") ∧ "p3" ⟫
#eval TrueQBF [(∀, "p1"), (∀, "p2"), (∃, "p3"), (∀, "p4")] ⟪ (("p1" ∧ "p2") → "p4") ∨ ¬"p3" ⟫
#eval TrueQBF [(∀, "p1"), (∃, "p2")] ⟪ "p2" ∧ "p1" ⟫
#eval ⟪ "p2" ∧ "p1" ⟫.replace_atom_bot "p2"
