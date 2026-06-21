structure FuncSymbol (α : Type u) where
arity : Nat
name : α

inductive Term (α : Type u) : Type _ where
| var : α -> Term α
| func (f : FuncSymbol α) : (Fin f.arity -> Term α) -> Term α

namespace Term

def from_list {α : Type u} (f : FuncSymbol α) (l : List (Term α)) (len : l.length = f.arity) : Term α :=
Term.func f (fun n => l.get (n.cast (by grind)))

def make_constant {α : Type u} (idx : α) : Term α := from_list (FuncSymbol.mk 0 idx) (@List.nil (Term α)) (by grind)

def vars : Term α -> List α
| .var x => [x]
|.func f ts => Fin.foldl f.arity (fun l x => l ++ (ts x).vars) []

def size : Term α -> Nat
| var _ => 1
| func f ts => 1 + Fin.foldl f.arity (fun l x => l + (ts x).size) 0

theorem size_sum_ge_start (n : Nat) (f : Fin n -> Term α) : ∀ start, Fin.foldl n (fun l x => l + (f x).size) start ≥ start := by
  induction n with
  | zero => grind
  | succ n ih =>
    intro start
    let f' : Fin n -> Term α := fun x => f x.succ
    rw [Fin.foldl_succ]
    specialize ih f' (start + (f 0).size)
    grind

theorem size_gt_zero : (T : Term α) -> T.size > 0 := by intro T; unfold size; grind

theorem size_gt_one  {α : Type u} (i : α) (n : Nat) (n_gt : n > 0) (F : FuncSymbol α) (F_eq : F = FuncSymbol.mk n i) (t : Fin F.arity -> Term α) : (Term.func F t).size > 1 := by
  suffices ∀ n (f : Fin n -> Term α) start, Fin.foldl n (fun l x => l + (f x).size) start ≥ start by
    unfold size
    cases n with
    | zero =>
      grind
    | succ n =>
      have a_eq : F.arity = n+1 := by grind
      simp only [a_eq]
      rw [Fin.foldl_succ]
      symm at a_eq
      let t' : Fin n -> Term α := fun x => t ((x.succ).cast (a_eq))
      specialize this n t'
      simp only [t'] at this
      simp only [Nat.zero_add, gt_iff_lt, Nat.lt_add_right_iff_pos]
      let z : Fin F.arity := Fin.mk 0 (by grind)
      specialize this (t z).size
      apply Nat.lt_of_lt_of_le _ this
      unfold size; grind
  intro n f
  induction n with
  | zero => grind
  | succ n ih =>
    let f' : Fin n -> Term α := fun x => f x.succ
    intro start
    rw [Fin.foldl_succ]
    specialize ih f' (start + (f 0).size)
    grind

def args : Term α -> List (Term α)
| var _ => []
| func f t => Fin.foldl f.arity (fun l x => l ++ [(t x)]) []

def toString [ToString α] : Term α -> String
| var x => s!"x_{ToString.toString x} "
| func f t => if f.arity == 0 then s!"c_{f.name}" else (Fin.foldl f.arity (fun s x => s ++ s!"{toString (t x)}" ++ " ") s!"f_{f.name}(") ++ ")"

instance [ToString α] : ToString (Term α) where
  toString := Term.toString

end Term

structure PredSymbol (α : Type u) where
arity : Nat
name : α

abbrev Tuple (n : Nat) (α : Type u) := Fin n -> α

namespace Tuple

def from_list {α : Type u} (l : List α) : Fin l.length -> α := fun x => l.get x

def toString {α : Type u} {n : Nat} [ToString α] (t : Tuple n α) : String :=
"(" ++ (Fin.foldl n (fun s x => s ++ ToString.toString (t x) ++ " ") "") ++ ")"

instance [ToString α] {n : Nat} : ToString (Tuple n α) where
  toString := Tuple.toString

end Tuple


def from_pred {α : Type u} (l : List α) (p : PredSymbol α) (eq : p.arity = l.length) : Fin p.arity -> α :=
fun x => l.get (x.cast eq)

syntax (name := tuple) "ₜ(" withoutPosition(term,*,?) ")" : term
syntax ident "❰" withoutPosition(term,*,?) "❱" : term

namespace Lean

macro_rules
| `(ₜ( $elems,* )) => do `(Tuple.from_list [$(elems),*])

#eval ₜ(1, 2, 3)
#check ₜ('a','b')


end Lean

inductive Formula (P T : Type u) : Type u
| atom (p : PredSymbol P) : (Fin p.arity -> Term T) -> Formula P T
| not : Formula P T -> Formula P T
| and  : Formula P T -> Formula P T -> Formula P T
| or : Formula P T -> Formula P T -> Formula P T
| eq : Formula P T -> Formula P T -> Formula P T
| imp : Formula P T -> Formula P T  -> Formula P T
| for_all : T -> Formula P T -> Formula P T
| éxists : T -> Formula P T -> Formula P T

variable {P T : Type u}

namespace Formula

def atom_from_list (p : PredSymbol P) (l : List (Term T)) (a_eq : p.arity = l.length) : Formula P T :=
  .atom p (fun n => l.get (n.cast a_eq))

def variables : Formula P T -> List T
| atom p t => Fin.foldl p.arity (fun l x => l ++ (t x).vars) []
| not F => F.variables
| and F G => F.variables ++ G.variables
| or F G => F.variables ++ G.variables
| imp F G => F.variables ++ G.variables
| eq F G => F.variables ++ G.variables
| for_all x F => F.variables -- ist eine variable teil der formel, wenn sie beim quantor steht aber sonst nirgendwo?
| éxists x F => F.variables

def free_variables [BEq T] : Formula P T -> List T
| atom p t => Fin.foldl p.arity (fun l x => l ++ (t x).vars) []
| not F => F.free_variables
| and F G => F.free_variables ++ G.free_variables
| or F G => F.free_variables ++ G.free_variables
| imp F G => F.free_variables ++ G.free_variables
| eq F G => F.free_variables ++ G.free_variables
| for_all x F => F.free_variables.removeAll [x]
| éxists x F => F.free_variables.removeAll [x]

def closedFormula [BEq T] : Formula P T -> Prop := fun F => F.free_variables = []

def openFormula [BEq T] : Formula P T -> Prop := fun F => ¬F.closedFormula

def toString [ToString P] [ToString T] : Formula P T -> String
| .atom p t => s!"p_{p.name}" ++ Fin.foldl p.arity (fun s x => s ++ (t x).toString) "(" ++ ")"
| .not f => s!"¬{toString f}"
| .and f g => s!"({toString f} ∧ {toString g})"
| .or f g => s!"({toString f} ∨ {toString g})"
| .imp f g => s!"({toString f} -> {toString g})"
| .eq f g => s!"({toString f} ↔ {toString g})"
| .éxists v f => s!"∃x{v}.{toString f}"
| .for_all v f => s!"∀x{v}.{toString f}"

instance [ToString P] [ToString T] : ToString (Formula P T) where
  toString := Formula.toString

end Formula

structure Interpretation (P T Δ : Type u) where
  f_Terms (f : FuncSymbol T) : (Fin f.arity -> Δ) -> Δ
  f_Pred (p : PredSymbol P) : (Fin p.arity -> Δ) -> Prop

def Assignment (T Δ : Type u) := T -> Δ

def Assignment.map_var  {T Δ : Type u} [DecidableEq T] (Z : Assignment T Δ) (x : T) (δ : Δ) : Assignment T Δ :=
fun y => if y = x then δ else Z y

variable {Δ : Type u}

namespace Interpretation

def eval_term (I : Interpretation P T Δ) (Z : Assignment T Δ) : Term T -> Δ
| Term.var x => Z x
| Term.func f t => I.f_Terms f (fun x => I.eval_term Z (t x))

def eval_atom (I : Interpretation P T Δ) (Z : Assignment T Δ) (p : PredSymbol P) (t : Fin p.arity -> Term T) : Prop :=
I.f_Pred p (fun x => I.eval_term Z (t x))

def eval [DecidableEq T] (I : Interpretation P T Δ) (Z : Assignment T Δ) : Formula P T -> Prop
| .atom p t => I.eval_atom Z p t
| .not F => ¬(I.eval Z F)
| .and F G => (I.eval Z F) ∧ (I.eval Z G)
| .or F G => (I.eval Z F) ∨ (I.eval Z G)
| .imp F G => (I.eval Z F) → (I.eval Z G)
| .eq F G => (I.eval Z F) ↔ (I.eval Z G)
| .for_all x F => ∀ (δ : Δ), I.eval (Z.map_var x δ) F
| .éxists x F => ∃ (δ : Δ), I.eval (Z.map_var x δ) F

end Interpretation

def P0 := {name := 0, arity := 2 : PredSymbol Nat}

def x0 := Term.var 0
def x1 := Term.var 1
def x2 := Term.var 2

def φ1 : (Formula Nat Nat) := .for_all 0 (.for_all 1 (.eq (Formula.atom_from_list P0 [x0, x1] (by simp only [P0]; grind)) (Formula.atom_from_list P0 [x0, x1] (by simp only [P0]; grind))))
#eval φ1

def t_1 : Fin P0.arity -> Nat := from_pred [0,1] P0 (by simp [P0])

def from_list_with_arity {α : Type u} (n : Nat) (l : List α) (eq : n = l.length) : Fin n → α :=
  fun x => l.get (x.cast eq)

def test := from_list_with_arity P0.arity [1,0] (by simp only [P0]; grind)

instance : OfNat (Fin P0.arity) i := by

  sorry

def t_1' : Fin P0.arity -> Nat := fun n => match n with
| 0 => 1
| 1 => 0

#check t_1'

def I1 : Interpretation Nat Nat Nat where
f_Terms := fun _ _ => 0                --- 0_o
f_Pred := fun p t => match p,t with
| P0, t => t = t_1'  --∨ t = t_2 ∨ t = t_3
| _, _ => False

def Z1 : Assignment Nat (Fin 2) := fun _ => 0

theorem test : I1.eval Z1 φ1 := by
  unfold Interpretation.eval φ1
  simp only [Fin.forall_fin_two, Fin.isValue]
  unfold Interpretation.eval Assignment.map_var Formula.atom_from_list
  simp only [Fin.isValue, List.length_cons, List.length_nil, Nat.reduceAdd, List.get_eq_getElem, Fin.forall_fin_two]
  unfold Interpretation.eval
  grind

#eval φ1


declare_syntax_cat formula
declare_syntax_cat p_atom
syntax (name := atom) ident "(" withoutPosition(term,*,?) ")"     : p_atom
syntax p_atom                                                     : formula
syntax:50 formula:50 " ∨ " formula:51                             : formula
syntax:60 formula:60 " ∧ " formula:61                             : formula
syntax:70 "¬"formula:70                                           : formula
syntax:40 formula:40 " → " formula:41                             : formula
syntax:30 formula:30 " ↔ " formula:31                             : formula
syntax:20 "∃" ident "." formula:21                                : formula
syntax:20 "∀" ident "." formula:21                                : formula
syntax " (" formula ") "                                          : formula
syntax "⌜" formula "⌟"                                            : term


macro_rules
| `(⌜ $p_sym:ident( $elems,* )⌟)  => do `(Formula.atom_from_list $p_sym [$(elems),*] (by unfold $p_sym; grind))
| `(⌜ ¬$F:formula ⌟)              => `(Formula.not ⌜ $F ⌟)
| `(⌜ $F:formula ∨ $G:formula ⌟)  => `(Formula.or (⌜ $F ⌟) (⌜ $G ⌟))
| `(⌜ $F:formula ∧ $G:formula ⌟)  => `(Formula.and (⌜ $F ⌟) (⌜ $G ⌟))
| `(⌜ $F:formula → $G:formula ⌟)  => `(Formula.imp (⌜ $F ⌟) (⌜ $G ⌟))
| `(⌜ $F:formula ↔ $G:formula ⌟)  => `(Formula.eq (⌜ $F ⌟) (⌜ $G ⌟))
| `(⌜ ∃ $p:ident. ($F:formula) ⌟) => `(Formula.éxists $p (⌜ $F ⌟))
| `(⌜ ∀ $p:ident. ($F:formula) ⌟) => `(Formula.for_all $p (⌜ $F ⌟))
| `(⌜ ( $F ) ⌟) => `(⌜ $F ⌟)

def y0 := 0
def y1 := 1
def Y0 := Term.var y0
def Y1 := Term.var y1
def Y2 := Term.var 2

def f1 := {arity := 3, name := 1 : FuncSymbol Nat}
def T1 := Term.from_list f1 [Y1, Y2, Y0] (by unfold f1; grind)
#eval T1

def F : Formula Nat Nat := ⌜ ∀y0. (∃y1. (P0(T1,Y1) → P0(Y1,Y0))) ⌟
#eval F
