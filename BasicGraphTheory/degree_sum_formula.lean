import BasicGraphTheory.inductive_graphs
import BasicGraphTheory.relation_to_SimpleGraph
import BasicGraphTheory.auxiliary_lemmas


theorem sum_of_degrees_twice_of_edges {n} (g: simple_graph n):
  ∑ (i ∈ Finset.range n), degree g i = 2 * (edges g).length := by
  cases g; rename_i g Hg
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
                       simp at *
                       intros H
                       omega
                     apply aux05 at H
                     rw [H]; clear H
                     have H: ∑ x ∈ Finset.range m, (if x ∈ h then m :: neighbors_aux t x else neighbors_aux t x).length =
                             ∑ x ∈ Finset.range m, (neighbors_aux t x).length + h.length := by
                       have H: ∀ x, (if x ∈ h then m :: neighbors_aux t x else neighbors_aux t x).length = (if x ∈ h then (neighbors_aux t x).length + 1 else (neighbors_aux t x).length) := by
                         intros x
                         split_ifs <;> simp
                       simp_rw [H]; clear H
                       convert (aux04 m h Hg2 Hg1 (fun x => (neighbors_aux t x).length))
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
                     have H0: ∀ y, y ∈ neighbors_aux t m → False := by
                       intros y Hy
                       have H1: adjacent ⟨t, Hg3⟩ m y := by
                         unfold adjacent neighbors
                         simp
                         assumption
                       have H2 := size_limit_on_adjacent_nodes m y _ H1
                       omega
                     generalize (neighbors_aux t m) = W at *
                     cases W
                     . simp
                       omega
                     . rename_i head tail
                       simp at H0
                       have H1 := H0 head
                       tauto
