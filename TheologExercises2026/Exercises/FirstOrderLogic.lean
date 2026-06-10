
namespace Fin

end Fin

inductive Term (α : Type u) : Type _ where
| var : α -> Term α
| func (idx : Nat) (arity : Nat) : (Fin arity -> Term α) -> Term α

namespace Term

def from_list {α : Type u} (idx : Nat) (l : List (Term α)) : Term α :=
Term.func idx l.length (fun n => l.get n)

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
| var x => s!"x{ToString.toString x}"
| func idx n f => if n == 0 then s!"c{idx}" else (Fin.foldl n (fun s x => s ++ s!"{toString (f x)}" ++ " ") s!"f{idx}(") ++ ")"

instance [ToString α] : ToString (Term α) where
  toString := Term.toString

end Term

def x0 := Term.var 3
def x1 := Term.var 1
def x2 := Term.var 2

def k := [x0, x2]
def l := [x0, x1, x2, (Term.from_list 0 k)]
def t0 := Term.from_list 0 k
def t1 := Term.from_list 1 l
#eval! t1--.toString
#eval t1.vars
#eval t1.size
def e : List (Term Nat) := []
#eval Term.from_list 1 e


inductive Formula : Type u
| atom (idx : Nat) (arity : Nat) : (Fin arity -> Term Nat) -> Formula
| not : Formula -> Formula
| and  : Formula -> Formula -> Formula
| or : Formula -> Formula -> Formula
| eq : Formula -> Formula -> Formula
| imp : Formula -> Formula -> Formula
| for_all : Nat -> Formula -> Formula
| éxists : Nat -> Formula -> Formula

namespace Formula

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

end Formula
