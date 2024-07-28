import Mathlib
import BasicGraphTheory.inductive_graphs

def edges_aux {n} (g: pre_simple_graph n): List (Nat × Nat) :=
  match g with
  | .Empty => []
  | .Cons m h t => edges_aux t ++ List.map (λ x => (m, x)) h

def edges {n} (g: simple_graph n) := edges_aux g.1

def edges_correctness {n} (g: simple_graph n): ∀ x y, y < x → ((x, y) ∈ edges g ↔ adjacent g x y) := by
  cases g
  rename_i g Hg
  induction g with
  | Empty => intros x y H
             unfold edges edges_aux adjacent neighbors neighbors_aux
             simp
  | Cons _ h t iH => intros x y H
                     simp at *
                     obtain ⟨Hg1, Hg2, Hg3⟩ := Hg
                     rw [edges, edges_aux]
                     simp
                     unfold edges at iH
                     simp at *
                     rw [iH] <;> try assumption
                     clear iH
                     unfold adjacent neighbors
                     simp
                     constructor <;> intro H0
                     . unfold neighbors_aux
                       split_ifs with H1 H2
                       . simp
                         tauto
                       . simp
                         obtain H0 | H0 := H0
                         . tauto
                         . apply Hg2 at H2
                           linarith
                       . obtain H0 | H0 := H0
                         . assumption
                         . tauto
                     . unfold neighbors_aux at H0
                       split_ifs at H0 with H1 H2
                       . simp at *
                         tauto
                       . simp at *
                         obtain H0 | H0 := H0
                         . apply Hg2 at H2
                           linarith
                         . tauto
                       . tauto

def sum_aux00 A B (f: A → B) x a b [Decidable x]: f (if x then a else b) = if x then f a else f b := by
  split_ifs <;> simp

def sum_aux01 n (f g: Nat → Nat): (∀ x ∈ Finset.range n, f x = g x) → (∑ x ∈ Finset.range n, f x) = (∑ x ∈ Finset.range n, g x) := by
  intros H
  have H0: ∀ (x: Finset.range n), f x = g x := by
    intros x
    cases x; rename_i x Hx
    simp
    tauto
  apply Finset.sum_congr <;> simp at *
  assumption

theorem aux02 n (g: simple_graph n) k (Hk: n ≤ k): neighbors g k = [] := by
  cases g; rename_i g Hg
  induction n with
  | zero => unfold neighbors neighbors_aux
            split
            . simp
            . linarith
  | succ m iH => cases g; rename_i h g
                 unfold neighbors neighbors_aux
                 split_ifs with H H1
                 . linarith
                 . obtain ⟨Hg1, Hg2, Hg3⟩ := Hg
                   apply Hg2 at H1
                   linarith
                 . obtain ⟨Hg1, Hg2, Hg3⟩ := Hg
                   apply iH at Hg3
                   unfold neighbors at Hg3
                   simp at Hg3
                   . assumption
                   . linarith

theorem sum_aux02 (m: Nat) (h: List Nat) (H: ∀ x ∈ h, x < m) (H0: h.Nodup) (f: Nat → Nat):
  ∑ x ∈ Finset.range m, (if x ∈ h then f x + 1 else f x) = ∑ x ∈ Finset.range m, f x + h.length := by
  have H1: ∀ x, (if x ∈ h then f x + 1 else f x) = (f x + if x ∈ h then 1 else 0) := by
    intros
    split <;> simp
  simp_rw [H1, Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero]
  simp
  clear H1 f
  induction h with
  | nil => simp
  | cons x t iH => simp at *
                   rw [Finset.filter_or]
                   simp
                   split_ifs with H1
                   . rw [Finset.card_union_of_disjoint]
                     . simp
                       rw [iH] <;> tauto
                       omega
                     . simp
                       tauto
                   . omega


theorem sum_of_degrees_twice_of_edges {n} (g: simple_graph n):
  ∑ (i ∈ Finset.range n), degree g i = 2 * (edges g).length := by
  cases g
  rename_i g Hg
  induction g with
  | Empty => simp
             unfold edges edges_aux
             rfl
  | Cons m h t iH => rw [Finset.sum_range_succ]
                     obtain ⟨Hg1, Hg2, Hg3⟩ := Hg
                     unfold degree neighbors neighbors_aux
                     simp
                     have H: ∀ x ∈ Finset.range m,
                        (if m = x then h ++ neighbors_aux t x else if x ∈ h then m :: neighbors_aux t x else neighbors_aux t x).length =
                        (if x ∈ h then m :: neighbors_aux t x else neighbors_aux t x).length := by
                       intros x Hx
                       congr 1
                       simp at Hx
                       simp at *
                       intros H
                       omega
                     apply sum_aux01 at H
                     rw [H]
                     clear H
                     have H: ∑ x ∈ Finset.range m, (if x ∈ h then m :: neighbors_aux t x else neighbors_aux t x).length =
                             ∑ x ∈ Finset.range m, (neighbors_aux t x).length + h.length := by
                       have H: ∀ x, (if x ∈ h then m :: neighbors_aux t x else neighbors_aux t x).length = (if x ∈ h then (neighbors_aux t x).length + 1 else (neighbors_aux t x).length) := by
                         intros x
                         split_ifs
                         . simp
                         . simp
                       simp_rw [H]; clear H
                       apply sum_aux02 <;> assumption
                     rw [H]; clear H
                     unfold degree neighbors at iH
                     simp at iH
                     rw [iH Hg3]
                     unfold edges
                     have H: (edges_aux (pre_simple_graph.Cons m h t)).length = h.length + (edges_aux t).length := by
                       rw [edges_aux]
                       rw [List.length_append]
                       rw [List.length_map]
                       omega
                     simp
                     rw [edges_aux]
                     simp
                     clear iH H
                     have H := aux02 m ⟨t, Hg3⟩ m (by omega)
                     unfold neighbors at H
                     simp at H
                     rw [H]
                     simp
                     omega
