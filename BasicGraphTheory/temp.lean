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

theorem aux00 (n w: Nat) (H: w < n):
  (Finset.filter (fun (x: Fin n) ↦ ↑x = w) Finset.univ).card = 1 := by
  rw [<- Finset.univ_map_subtype]
  simp
  have H0: ∃! (x: Fin n), ↑x = w := by
    exists ⟨w, H⟩
    simp
    intros y H0
    cases y
    simp at *
    assumption
  rw [<- unique_subtype_iff_exists_unique] at H0
  cases H0; rename_i H10
  apply Fintype.card_unique at H10
  apply H10

theorem aux01 (n: Nat) (L: List Nat) (H: ∀ x ∈ L, x < n) (H0: L.Nodup):
  (Finset.filter (fun (x: Fin n) ↦ ↑x ∈ L) Finset.univ).card = L.length := by
  rw [← Fintype.card_subtype]
  induction L with
  | nil => simp
  | cons head tail iH => simp at *
                         rw [Fintype.card_subtype_or_disjoint]
                         . rw [Fintype.card_subtype]
                           rw [aux00]
                           . rw [iH H.2 H0.2]
                             linarith
                           . tauto
                         . unfold Disjoint
                           intros f1 H1 H2
                           reduce at H1
                           reduce at H2
                           reduce
                           intros w Hw
                           have H3 := H1 _ Hw
                           have H4 := H2 _ Hw
                           rw [H3] at H4
                           tauto
