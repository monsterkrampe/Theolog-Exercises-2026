
namespace Fin

end Fin

inductive Term (α : Type u) : Type _ where
| var : α -> Term α
| func (idx : Nat) (arity : Nat) : (Fin arity -> Term α) -> Term α

namespace Term

def from_list {α : Type u} (idx : Nat) (l : List (Term α)) : Term α :=
Term.func idx l.length (fun n => l.get n)

def make_constant (idx : Nat) : Term Nat := from_list idx (@List.nil (Term Nat))

def vars : Term α -> List α
| .var x => [x]
|.func _ n f => Fin.foldl n (fun l x => l ++ (f x).vars) []

def size : Term α -> Nat
| var _ => 1
| func _ n f => 1 + Fin.foldl n (fun l x => l + (f x).size) 0

theorem size_gt_zero : (T : Term α) -> T.size > 0 := by intro T; unfold size; grind

theorem size_gt_one (idx n : Nat) (hn : n > 0) (f : Fin n -> Term α) : (Term.func idx n f).size > 1 := by
  induction n with
  | zero => grind
  | succ n ih =>
    unfold size
    rw [Fin.foldl_succ, Fin.foldl_eq_finRange_foldl]
    simp only [gt_iff_lt, Nat.lt_add_right_iff_pos]
    --have aux := size_gt_zero (α := α)
    --specialize aux (Term.func idx (n+1) f)
    by_cases n_gtz : 0 < n
    . let f' : Fin n -> Term α := fun x => f x.succ
      specialize ih n_gtz f'
      simp [f', size, Fin.foldl_eq_finRange_foldl] at ih

      sorry

    sorry

def args : Term α -> List (Term α)
| var _ => []
| func _ n f => Fin.foldl n (fun l x => l ++ [(f x)]) []

def contains [DecidableEq (Term α)] (T1 T2 : Term α) : Prop :=
if T1 = T2 then True else match T1 with
| var x => Term.var x = T2
| func _ n f => Fin.foldl n (fun l x => l ∨ (f x).contains T2) False

def depth : Term α -> Nat
| var _ => 0
| func _ n f => 1 + Fin.foldl n (fun d x => max d (f x).depth) 0

theorem args_length (idx n : Nat)  (f : Fin n -> Term α) : (func idx n f).args.length = n := by
  unfold args
  simp
  induction n with
  | zero => grind
  | succ m ih =>
    rw [Fin.foldl_succ, Fin.foldl_eq_finRange_foldl]
    let f' : Fin m -> Term α := fun x => f x.succ
    by_cases m_gtz : m > 0
    . specialize ih f'
      simp only [Fin.foldl_eq_finRange_foldl, f'] at ih
      simp only [List.nil_append, List.foldl_append_eq_append, List.cons_append, List.length_cons,
        List.length_flatten, List.map_map, Nat.add_right_cancel_iff] at *
      exact ih
    . grind

def toString [ToString α] : Term α -> String
| var x => s!"x{ToString.toString x} "
| func idx n f => if n == 0 then s!"c{idx}" else (Fin.foldl n (fun s x => s ++ s!"{toString (f x)}" ++ " ") s!"f{idx}(") ++ ")"

instance [ToString α] : ToString (Term α) where
  toString := Term.toString

end Term

def x0 := Term.var 0
def x1 := Term.var 1
def x2 := Term.var 2

def k := [x0, x2]
def l := [x0, x1, x2, (Term.from_list 0 k)]
def t0 := Term.from_list 0 k
def t1 := Term.from_list 1 l
#eval! t1--.toString
#eval t1.vars
#eval t1.size
#eval Term.make_constant 0

inductive Formula : Type u
| atom (idx arity : Nat) : (Fin arity -> Term Nat) -> Formula
| not : Formula -> Formula
| and  : Formula -> Formula -> Formula
| or : Formula -> Formula -> Formula
| eq : Formula -> Formula -> Formula
| imp : Formula -> Formula -> Formula
| for_all : Nat -> Formula -> Formula
| éxists : Nat -> Formula -> Formula

namespace Formula

def atom_from_list (idx : Nat) (l : List (Term Nat)) : Formula :=
  .atom idx l.length (fun n => l.get n)

def variables : Formula -> List Nat
| atom _ n f => Fin.foldl n (fun l x => l ++ (f x).vars) []
| not F => F.variables
| and F G => F.variables ++ G.variables
| or F G => F.variables ++ G.variables
| imp F G => F.variables ++ G.variables
| eq F G => F.variables ++ G.variables
| for_all x F => F.variables -- ist eine variable teil der formel, wenn sie beim quantor steht aber sonst nirgendwo?
| éxists x F => F.variables

def free_variables : Formula -> List Nat
| atom _ n f => Fin.foldl n (fun l x => l ++ (f x).vars) []
| not F => F.free_variables
| and F G => F.free_variables ++ G.free_variables
| or F G => F.free_variables ++ G.free_variables
| imp F G => F.free_variables ++ G.free_variables
| eq F G => F.free_variables ++ G.free_variables
| for_all x F => F.free_variables.removeAll [x]
| éxists x F => F.free_variables.removeAll [x]

def closedFormula : Formula -> Prop := fun F => F.free_variables = []

def openFormula : Formula -> Prop := fun F => ¬F.closedFormula

def toString  : Formula -> String
| .atom idx n f => s!"p{idx}" ++ Fin.foldl n (fun s t => s ++ (f t).toString) "(" ++ ")"
| .not f => s!"¬{toString f}"
| .and f g => s!"({toString f} ∧ {toString g})"
| .or f g => s!"({toString f} ∨ {toString g})"
| .imp f g => s!"({toString f} -> {toString g})"
| .eq f g => s!"({toString f} ↔ {toString g})"
| .éxists v f => s!"∃x{v}.{toString f}"
| .for_all v f => s!"∀x{v}.{toString f}"

instance : ToString Formula where
  toString := Formula.toString

end Formula

def a1 := Formula.atom_from_list 0 [x0, x1, x2]
def a2 := Formula.atom_from_list 1 [x1, x2]
def F1 : Formula := .for_all 0 (.and a1 a2)

structure Interpretation (Δ : Type u) where
  f_Terms (i n : Nat) : (Fin n -> Δ) -> Δ
  f_Pred (i n : Nat) : (Fin n -> Δ) -> Prop

def Assignment (Δ : Type u) := Nat -> Δ

def Assignment.map_var {Δ : Type u} (Z : Assignment Δ) (x : Nat) (δ : Δ) : Assignment Δ :=
fun y => if y = x then δ else Z y

variable {Δ : Type u}

namespace Interpretation

def eval_term (I : Interpretation Δ) (Z : Assignment Δ) : Term Nat -> Δ
| Term.var x => Z x
| Term.func i n f => I.f_Terms i n (fun x => I.eval_term Z (f x))

def eval_atom (I : Interpretation Δ) (Z : Assignment Δ) (i n : Nat) (f : Fin n -> Term Nat) : Prop :=
I.f_Pred i n (fun x => I.eval_term Z (f x))

def eval (I : Interpretation Δ) (Z : Assignment Δ) : Formula -> Prop
| .atom i n f => I.eval_atom Z i n f
| .not F => ¬(I.eval Z F)
| .and F G => (I.eval Z F) ∧ (I.eval Z G)
| .or F G => (I.eval Z F) ∨ (I.eval Z G)
| .imp F G => (I.eval Z F) → (I.eval Z G)
| .eq F G => (I.eval Z F) ↔ (I.eval Z G)
| .for_all x F => ∀ (δ : Δ), I.eval (Z.map_var x δ) F
| .éxists x F => ∃ (δ : Δ), I.eval (Z.map_var x δ) F

end Interpretation

def φ1 : Formula := .for_all 0 (.for_all 1 (.eq (Formula.atom_from_list 0 [x0, x1]) (Formula.atom_from_list 0 [x0, x1])))

def t_1 : Fin 2 -> Fin 2 := fun n =>
match n with
| 0 => 0
| 1 => 1

def t_2 : Fin 2 -> Fin 2 := fun n => match n with
| 0 => 1
| 1 => 0

def t_3 : Fin 2 -> Fin 2 := fun n => match n with
| 0 => 1
| 1 => 1

def I1 : Interpretation (Fin 2) where
f_Terms := fun _ _ _ => 0                --- 0_o
f_Pred := fun i n => match i,n with
| 0, 2 => fun t => t = t_1 ∨ t = t_2 ∨ t = t_3
| _, _ => fun _ => False

def Z1 : Assignment (Fin 2) := fun _ => 0

theorem test : I1.eval Z1 φ1 := by
  unfold Interpretation.eval φ1
  simp only [Fin.forall_fin_two, Fin.isValue]
  unfold Interpretation.eval Assignment.map_var Formula.atom_from_list
  simp only [Fin.isValue, List.length_cons, List.length_nil, Nat.reduceAdd, List.get_eq_getElem, Fin.forall_fin_two]
  unfold Interpretation.eval
  grind
