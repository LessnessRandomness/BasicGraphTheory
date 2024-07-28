import Mathlib

theorem H (m: Nat) (h: List Nat) (H: ∀ x ∈ h, x < m) (H0: h.Nodup) (f: Nat → Nat):
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
