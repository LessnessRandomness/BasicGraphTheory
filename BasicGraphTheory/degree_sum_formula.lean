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


instance adjacent_decidable: ∀ {n} (g: simple_graph n), DecidableRel (adjacent g) := by
  intros n g x y
  unfold adjacent
  infer_instance

-- theorem list_filter_or {A} (L: List A) (f g: A → Bool) x:
--   x ∈ List.filter (λ x => f x || g x) L ↔ (x ∈ List.filter f L ∨ x ∈ List.filter g L) := by
--   induction L with
--   | nil => simp
--   | cons head tail iH => repeat rw [List.filter_cons]
--                          simp
--                          split_ifs with H1 H2 H3 H4
--                          . simp
--                            rw [iH]
--                            tauto
--                          . simp
--                            rw [iH]
--                            tauto
--                          . simp
--                            rw [iH]
--                            tauto
--                          . tauto
--                          . tauto
--                          . tauto
--                          . tauto
--                          . tauto

-- theorem neighbors_set_of_all_adjacent {n} (g: simple_graph n) (x v: Nat):
--   v ∈ neighbors g x ↔ v ∈ List.filter (fun y => Decidable.decide (adjacent g x y)) (List.finRange n) := by
--   cases g; rename_i g H
--   induction n with
--   | zero => simp at *
--             unfold neighbors neighbors_aux
--             split
--             . simp
--             . linarith
--   | succ m iH => have H4: ∀ (A B: Type) (f: A → B) (L: List A), L.bind (fun a => [f a]) = List.map f L := by
--                      intros A B f L
--                      induction L with
--                      | nil => simp
--                      | cons head tail iH => simp
--                                             assumption
--                  simp at *
--                  rw [H4] at *
--                  cases g; rename_i h t
--                  unfold neighbors at *
--                  simp at *
--                  rw [neighbors_aux]
--                  obtain ⟨H1, H2, H3⟩ := H
--                  split_ifs with H4 H5
--                  . cases H4
--                    simp
--                    rw [iH _ H3]
--                    rw [List.range_succ]
--                    simp
--                    rw [List.filter_singleton]
--                    rw [Bool.cond_decide]
--                    have H5 := adjacent_irrefl ⟨pre_simple_graph.Cons x h t, ⟨H1, H2, H3⟩⟩ x
--                    split_ifs <;> try tauto
--                    simp
--                    unfold adjacent neighbors
--                    simp
--                    have H6: ∀ y, y ∈ neighbors_aux (.Cons x h t) x ↔
--                                  y ∈ h ∨ y ∈ neighbors_aux t x := by
--                      intros
--                      rw [neighbors_aux]
--                      simp
--                    simp_rw [H6]
--                    simp
--                    rw [list_filter_or]
--                    have H7: ∀ v, v ∈ List.filter (λ y => y ∈ h) (List.range x) ↔ v ∈ h := by
--                      rename_i H'
--                      clear H' H5 H3 iH H6 t H4 v
--                      induction h with
--                      | nil => simp
--                      | cons head tail iH => simp at *
--                                             intros v
--                                             rw [list_filter_or]
--                                             rw [iH H1.2 H2.2]
--                                             rw [List.filter_eq]
--                                             simp
--                                             have H3: List.count head (List.range x) = 1 := by
--                                               clear iH
--                                               apply List.count_eq_one_of_mem
--                                               . apply List.nodup_range
--                                               . rw [List.mem_range]
--                                                 tauto
--                                             have H4: ¬ List.count head (List.range x) = 0 := by omega
--                                             tauto
--                    rw [H7]
--                  . simp
--                    rw [iH _ H3]
--                    rw [List.range_succ]
--                    simp
--                    rw [List.filter_singleton]
--                    rw [Bool.cond_decide]
--                    split_ifs with H6
--                    . simp
--                      have H7: ∀ y, adjacent ⟨pre_simple_graph.Cons m h t, ⟨H1, H2, H3⟩⟩ x y ↔
--                                    y ∈ if m = x then h ++ neighbors_aux t x else if x ∈ h then m :: neighbors_aux t x else neighbors_aux t x := by
--                        intros y
--                        unfold adjacent neighbors at *
--                        simp
--                        rw [neighbors_aux]
--                      simp_rw [H7]
--                      have H8: ∀ y, (y ∈ if m = x then h ++ neighbors_aux t x else if x ∈ h then m :: neighbors_aux t x else neighbors_aux t x) ↔
--                               (if m = x then y ∈ h ++ neighbors_aux t x else if x ∈ h then y ∈ m :: neighbors_aux t x else y ∈ neighbors_aux t x) := by
--                        intros y
--                        split_ifs; tauto
--                      simp_rw [H8]
--                      simp_rw [decide_ite]
--                      have H9: ∀ y, (if m = x then decide (y ∈ h ++ neighbors_aux t x)
--                               else if x ∈ h then decide (y ∈ m :: neighbors_aux t x) else decide (y ∈ neighbors_aux t x)) =
--                               (decide (y ∈ m :: neighbors_aux t x)) := by
--                        split_ifs
--                        simp
--                      simp_rw [H9]
--                      unfold adjacent neighbors
--                      simp
--                      simp_rw [list_filter_or]
--                      have H10: List.filter (fun x => decide (x = m)) (List.range m) = [] := by
--                        sorry
--                      rw [H10]
--                      simp
--                      tauto
--                    . simp
--                      sorry
--                  . sorry

theorem list_bind_list_map: ∀ (A B: Type) (f: A → B) (L: List A), L.bind (fun a => [f a]) = List.map f L := by
  intros A B f L
  induction L with
  | nil => simp
  | cons head tail iH => simp
                         assumption

-- theorem degree_aux00 {n} (G: SimpleGraph (Fin n)) v [DecidableRel G.Adj]:
--   (G.neighborFinset v) = (λ (w: Fin n) => ↑w ∈ neighbors (SimpleGraph_to_simple_graph G) ↑v).toFinset := by
--   ext
--   simp
--   rw [adj_proof_2]
--   unfold adjacent
--   tauto


theorem aux03 (n w: Nat) (H: w < n):
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

theorem aux04 (n: Nat) (L: List Nat) (H: ∀ x ∈ L, x < n) (H0: L.Nodup):
  (Finset.filter (fun (x: Fin n) ↦ ↑x ∈ L) Finset.univ).card = L.length := by
  rw [← Fintype.card_subtype]
  induction L with
  | nil => simp
  | cons head tail iH => simp at *
                         rw [Fintype.card_subtype_or_disjoint]
                         . rw [Fintype.card_subtype]
                           rw [aux03]
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

theorem neighbors_lemma00 {n} g:
  ∀ h (H0: correct_simple_graph (.Cons n h g)) m (Hm: n ≤ m), neighbors_aux g m = [] := by
  induction g with
  | Empty => unfold neighbors_aux
             simp
  | Cons m h' g' iH => intros h H0
                       obtain ⟨H4, H5, H6⟩ := H0
                       unfold neighbors_aux
                       intros m1 Hm1
                       split_ifs with H7 H8
                       . omega
                       . obtain ⟨H9, H10, H11⟩ := H6
                         apply H10 at H8
                         omega
                       . apply iH
                         . exact H6
                         . omega


theorem neighbors_Nodup {n} (g: simple_graph n) x: (neighbors g x).Nodup := by
  sorry

def remove_last_from_pre_simple_graph {n} (g: pre_simple_graph (n + 1)): pre_simple_graph n :=
  match g with | .Cons _ h g' => g'

theorem aux05 {n} (G: SimpleGraph (Fin (n + 1))) [inst: DecidableRel G.Adj]:
  (SimpleGraph_to_simple_graph (remove_last G)).1 = remove_last_from_pre_simple_graph (SimpleGraph_to_simple_graph G).1 := by
  unfold remove_last remove_last_from_pre_simple_graph
  unfold SimpleGraph_to_simple_graph SimpleGraph_to_pre_simple_graph
  simp at *
  induction n with
  | zero => congr
  | succ m iH => congr

theorem degree_conserved {n} (G: SimpleGraph (Fin n)) v [inst: DecidableRel G.Adj]:
  G.degree v = degree (SimpleGraph_to_simple_graph G) v := by
  unfold SimpleGraph.degree
  unfold SimpleGraph.neighborFinset SimpleGraph.neighborSet
  simp_rw [adj_proof_2]
  unfold adjacent degree neighbors
  simp
  have H: (SimpleGraph_to_simple_graph G).1 = SimpleGraph_to_pre_simple_graph G inst := by
    unfold SimpleGraph_to_simple_graph
    simp
  have aux: (neighbors_aux (SimpleGraph_to_simple_graph G).1 ↑v).Nodup := by
    have H0 := neighbors_Nodup (SimpleGraph_to_simple_graph G) ↑v
    unfold neighbors at H0
    exact H0
  have aux0: ∀ y ∈ neighbors_aux (SimpleGraph_to_simple_graph G).1 ↑v, y < n := by
    intros y Hy
    apply aux00 at Hy
    tauto
  generalize (neighbors_aux (SimpleGraph_to_simple_graph G).1 ↑v) = W at *
  apply aux04
  . assumption
  . assumption



theorem sum_degrees_eq_twice_card_edges_Fin_variant {n} (G: SimpleGraph (Fin n)) [DecidableRel G.Adj]:
  ∑ v, G.degree v = 2 * G.edgeFinset.card := by

  sorry
