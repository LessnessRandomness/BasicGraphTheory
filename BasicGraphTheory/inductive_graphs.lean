import Batteries.Data.Fin.Basic
import Batteries.Data.Fin.Lemmas
import Mathlib

-- inductive simple_graph: Nat → Type :=
--   | Empty: simple_graph 0
--   | Cons: forall n, Set (Fin (n + 1)) → simple_graph n → simple_graph (n + 1)


inductive pre_simple_graph: Nat → Type :=
  | Empty: pre_simple_graph 0
  | Cons: forall n, List Nat → pre_simple_graph n → pre_simple_graph (n + 1)

def correct_simple_graph {n} (g: pre_simple_graph n): Prop :=
  match g with
  | .Empty => True
  | .Cons _ h t => h.Nodup ∧ (∀ x, x ∈ h → x < n) ∧ correct_simple_graph t

def simple_graph n := { g: pre_simple_graph n // correct_simple_graph g}

def neighbors_aux {n} (g: pre_simple_graph n) (x: Nat): List Nat :=
  match g with
  | .Empty => []
  | .Cons m L g' => if n = x
                    then L
                    else if x ∈ L
                         then n :: neighbors_aux g' x
                         else neighbors_aux g' x

def neighbors {n} (g: simple_graph n) (x: Nat): List Nat := neighbors_aux g.1 x

def adjacent {n} (g: simple_graph n) (x y: Nat): Prop := y ∈ neighbors g x

theorem adjacent_symm {n} (g: simple_graph n) (x y: Nat): adjacent g x y → adjacent g y x := by
  sorry

theorem adjacent_irrefl {n} (g: simple_graph n) (x: Nat): adjacent g x x → False :=
  sorry


-- Lemmas about fin --

theorem fin_to_nat_injective n: Function.Injective (λ (x: Fin n) => x.1) := by
  unfold Function.Injective
  intros x y h
  simp at *
  apply (Fin.ext h)

theorem fin_list_nodup n: (Fin.list n).Nodup := by
  sorry

-- by https://leanprover.zulipchat.com/#user/684366 (Edward van de Meent)
theorem fin_list_has_all_fins: ∀ {N} (f: Fin N), f ∈ Fin.list N := by
  intro n m
  refine List.mem_iff_get.mpr ?_
  have : m.val < (Fin.list n).length := by
    rw [Fin.length_list]
    exact m.2
  refine ⟨⟨m.val,this⟩,?_⟩
  simp only [List.get_eq_getElem, Fin.getElem_list, Fin.cast_mk, Fin.eta]

-- Complete Graph --

def pre_complete_graph (n: Nat): pre_simple_graph n :=
  match n with
  | 0 => .Empty
  | m + 1 => .Cons m (List.map (λ x => x.1) (Fin.list (m + 1))) (pre_complete_graph m)

theorem complete_graph_correct (n: Nat): correct_simple_graph (pre_complete_graph n) := by
  induction n with
  | zero => unfold pre_complete_graph correct_simple_graph
            simp
  | succ m iH => unfold pre_complete_graph correct_simple_graph
                 refine ⟨?_, ?_, ?_⟩
                 . exact List.Nodup.map (fin_to_nat_injective _) (fin_list_nodup _)
                 . intros x
                   intros H
                   simp at *
                   cases H; rename_i f H
                   obtain ⟨H0, H1⟩ := H
                   cases f
                   simp at *
                   omega
                 . assumption

def complete_graph (n: Nat): simple_graph n :=
  ⟨pre_complete_graph n, complete_graph_correct n⟩

#eval (neighbors (complete_graph 4) 0)
