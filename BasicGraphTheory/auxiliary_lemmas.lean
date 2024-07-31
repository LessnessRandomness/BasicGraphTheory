import Mathlib.Data.List.Range
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset

theorem aux00 {n} (f: Fin n): f ∈ List.finRange n := by
  refine List.mem_iff_get.mpr ?_
  have H: f.val < (List.finRange n).length := by
    rw [List.length_finRange]
    exact f.2
  refine ⟨⟨f.val, H⟩, ?_⟩
  simp only [List.get_eq_getElem, List.getElem_finRange, Fin.cast_mk, Fin.eta]

theorem aux01 (n w: Nat) (H: w < n): (Finset.filter (fun (x : Fin n) ↦ ↑x = w) Finset.univ).card = 1 := by
  rw [← Finset.card_singleton (⟨w, H⟩ : Fin n)]
  congr
  ext
  simp [Fin.ext_iff]

theorem aux02 (n: Nat) (L: List Nat) (H: ∀ x ∈ L, x < n) (H0: L.Nodup):
    (Finset.filter (fun (x: Fin n) ↦ ↑x ∈ L) Finset.univ).card = L.length := by
  rw [← List.toFinset_card_of_nodup H0, ← Finset.card_map ⟨_, Fin.val_injective⟩]
  congr
  ext i
  simpa [Fin.exists_iff] using H i

theorem aux03 A B (f: A → B) x a b [Decidable x]: f (if x then a else b) = if x then f a else f b := by
  split_ifs <;> simp

theorem aux04 (m: Nat) (h: List Nat) (H: ∀ x ∈ h, x < m) (H0: h.Nodup) (f: Nat → Nat):
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

theorem aux05 n (f g: Nat → Nat): (∀ x ∈ Finset.range n, f x = g x) → (∑ x ∈ Finset.range n, f x) = (∑ x ∈ Finset.range n, g x) := by
  intros H
  have H0: ∀ (x: Finset.range n), f x = g x := by
    intros x
    cases x; rename_i x Hx
    simp
    tauto
  apply Finset.sum_congr <;> simp at *
  assumption

theorem list_bind_list_map: ∀ (A B: Type) (f: A → B) (L: List A), L.bind (fun a => [f a]) = List.map f L := by
  intros A B f L
  induction L with
  | nil => simp
  | cons head tail iH => simp
                         assumption
