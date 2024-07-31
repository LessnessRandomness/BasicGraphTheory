import BasicGraphTheory.inductive_graphs
import BasicGraphTheory.auxiliary_lemmas


-- The theorem for simple_graph

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


-- The theorem for SimpleGraph (Fin n)

def remove_last_from_pre_simple_graph {n} (g: pre_simple_graph (n + 1)): pre_simple_graph n :=
  match g with | .Cons _ _ g' => g'



-- theorem SG_to_sg_of_remove_last {n} (G: SimpleGraph (Fin (n + 1))) [inst: DecidableRel G.Adj]:
--   (SimpleGraph_to_simple_graph (remove_last G)).1 = remove_last_from_pre_simple_graph (SimpleGraph_to_simple_graph G).1 := by
--   unfold remove_last remove_last_from_pre_simple_graph
--   unfold SimpleGraph_to_simple_graph SimpleGraph_to_pre_simple_graph
--   simp at *
--   induction n with
--   | zero => congr
--   | succ m iH => congr

-- theorem degree_conserved {n} (G: SimpleGraph (Fin n)) v [inst: DecidableRel G.Adj]:
--   G.degree v = degree (SimpleGraph_to_simple_graph G) v := by
--   unfold SimpleGraph.degree
--   unfold SimpleGraph.neighborFinset SimpleGraph.neighborSet
--   simp_rw [adj_proof_2]
--   unfold adjacent degree neighbors
--   simp
--   have H: (SimpleGraph_to_simple_graph G).1 = SimpleGraph_to_pre_simple_graph G inst := by
--     unfold SimpleGraph_to_simple_graph
--     simp
--   have aux: (neighbors_aux (SimpleGraph_to_simple_graph G).1 ↑v).Nodup := by
--     have H0 := neighbors_Nodup (SimpleGraph_to_simple_graph G) ↑v
--     unfold neighbors at H0
--     exact H0
--   have aux0: ∀ y ∈ neighbors_aux (SimpleGraph_to_simple_graph G).1 ↑v, y < n := by
--     intros y Hy
--     apply aux00 at Hy
--     tauto
--   generalize (neighbors_aux (SimpleGraph_to_simple_graph G).1 ↑v) = W at *
--   apply aux04
--   . assumption
--   . assumption

-- theorem finset_filter_ite {n} (p P1 P2: Fin n × Fin n → Prop)
--   [DecidablePred p] [DecidablePred P1] [DecidablePred P2]:
--   Finset.filter (fun x => if p x then P1 x else P2 x) Finset.univ =
--   Finset.filter (fun x => p x ∧ P1 x) Finset.univ ∪
--   Finset.filter (fun x => ¬ p x ∧ P2 x) Finset.univ := by
--   unfold Finset.filter
--   ext
--   simp
--   split_ifs <;> tauto

-- theorem finset_product_aux00 {n} (p q: Fin n → Prop)
--   [DecidablePred p] [DecidablePred q]:
--   (Finset.filter (fun (x: Fin n × Fin n) => p x.1 ∧ q x.2) Finset.univ).card =
--   (Finset.filter (fun (x: Fin n) => p x) Finset.univ).card *
--   (Finset.filter (fun (x: Fin n) => q x) Finset.univ).card := by
--   rw [<- Finset.univ_product_univ]
--   rw [Finset.filter_product]
--   exact Finset.card_product (Finset.filter p Finset.univ) (Finset.filter q Finset.univ)

-- theorem finset_aux01 {n} (p q: Fin n × Fin n → Prop) [DecidablePred p] [DecidablePred q]:
--   (Finset.filter (fun x => p x ∧ q x) Finset.univ).card +
--   (Finset.filter (fun x => ¬ p x ∧ q x) Finset.univ).card =
--   (Finset.filter (fun x => q x) Finset.univ).card := by
--   have H: (fun x => p x ∧ q x) = (fun x => q x ∧ p x) := by
--     ext; intros; tauto
--   have H0: (fun x => ¬ p x ∧ q x) = (fun x => q x ∧ ¬ p x) := by
--     ext; intros; tauto
--   simp_rw [H, H0]
--   rw [<- Finset.filter_filter]
--   rw [<- Finset.filter_filter]
--   rw [Finset.filter_card_add_filter_neg_card_eq_card]

-- theorem finset_aux02 {n} (P: Nat → Nat → Prop) (H: ∀ x y, P x y → x < n ∧ y < n) [DecidableRel P]:
--   (Finset.filter (fun (x: Fin n × Fin n) => P ↑x.1 ↑x.2) Finset.univ).card =
--   (Finset.filter (fun (x: Fin (n + 1) × Fin (n + 1)) => P ↑x.1 ↑x.2) Finset.univ).card := by
--   apply Finset.card_bij (fun x _ => (Fin.castSucc x.1, Fin.castSucc x.2))
--   · simp
--   · simp
--     intro ⟨a, ha⟩ ⟨b, hb⟩ h ⟨a', ha'⟩ ⟨hb, hb'⟩ h'
--     simp (config := {contextual := true}) [H _ _ h, H _ _ h']
--   · simp
--     intro ⟨a, ha⟩ ⟨b, hb⟩ h
--     specialize H _ _ h
--     use ⟨a, H.1⟩, ⟨b, H.2⟩
--     simpa using h

-- theorem sum_degrees_eq_twice_card_edges_Fin_variant {n} (G: SimpleGraph (Fin n)) [DecidableRel G.Adj]:
--   ∑ v, G.degree v = 2 * G.edgeFinset.card := by
--   simp_rw [degree_conserved]
--   have H := sum_of_degrees_twice_of_edges (SimpleGraph_to_simple_graph G)
--   rw [@Finset.sum_range] at H
--   rw [H]
--   clear H
--   rw [SimpleGraph.two_mul_card_edgeFinset]
--   simp_rw [adj_proof_2]
--   --
--   generalize (SimpleGraph_to_simple_graph G) = W
--   rename_i inst; clear inst G
--   cases W; rename_i g Hg
--   induction n with
--   | zero => cases g
--             simp at *
--             unfold edges edges_aux
--             simp
--   | succ m iH => cases g
--                  rename_i h g
--                  unfold edges edges_aux
--                  simp
--                  obtain ⟨Hg1, Hg2, Hg3⟩ := Hg
--                  have H := iH g Hg3
--                  unfold edges at H
--                  simp at H
--                  have H0: 2 * ((edges_aux g).length + h.length) = 2 * (edges_aux g).length + 2 * h.length := by
--                    omega
--                  rw [H0]
--                  rw [H]
--                  unfold adjacent neighbors
--                  simp_rw [neighbors_aux]
--                  have H1: ∀ x: Fin (m + 1) × Fin (m + 1), (↑x.2 ∈
--                           if m = ↑x.1 then h ++ neighbors_aux g ↑x.1
--                           else if ↑x.1 ∈ h then m :: neighbors_aux g ↑x.1 else neighbors_aux g ↑x.1) ↔
--                           (if m = ↑x.1 then ↑x.2 ∈ h ++ neighbors_aux g ↑x.1 else
--                            if ↑x.1 ∈ h then ↑x.2 ∈ m :: neighbors_aux g ↑x.1 else
--                            ↑x.2 ∈ neighbors_aux g ↑x.1) := by
--                    intros p
--                    split_ifs <;> tauto
--                  simp_rw [H1]
--                  clear iH H1 H H0
--                  simp
--                  repeat rw [finset_filter_ite]
--                  rw [Finset.card_union_of_disjoint]
--                  . have H: ∀ (x: Fin (m + 1) × Fin (m + 1)),
--                            (¬m = ↑x.1 ∧ if ↑x.1 ∈ h then ↑x.2 = m ∨ ↑x.2 ∈ neighbors_aux g ↑x.1 else ↑x.2 ∈ neighbors_aux g ↑x.1) ↔
--                            (if ↑x.1 ∈ h then ¬ m = ↑x.1 ∧ (↑x.2 = m ∨ ↑x.2 ∈ neighbors_aux g ↑x.1) else ¬ m = ↑x.1 ∧ ↑x.2 ∈ neighbors_aux g ↑x.1) := by
--                      intros x
--                      split_ifs <;> tauto
--                    simp_rw [H]
--                    clear H
--                    rw [finset_filter_ite]
--                    rw [Finset.card_union_of_disjoint]
--                    . have H: (fun (x: Fin (m + 1) × Fin (m + 1)) => m = ↑x.1 ∧ (↑x.2 ∈ h ∨ ↑x.2 ∈ neighbors_aux g ↑x.1)) =
--                              (fun (x: Fin (m + 1) × Fin (m + 1)) => m = ↑x.1 ∧ ↑x.2 ∈ h) := by
--                        ext; rename_i x
--                        constructor <;> intros H
--                        . obtain ⟨H1, H2⟩ := H
--                          rw [<- H1] at H2
--                          have H3 := aux02 m ⟨g, Hg3⟩ m (by omega)
--                          unfold neighbors at H3
--                          simp at H3
--                          rw [H3] at H2
--                          simp at H2
--                          tauto
--                        . tauto
--                      simp_rw [H]
--                      clear H
--                      have H: (fun (x: Fin (m + 1) × Fin (m + 1)) => ↑x.1 ∈ h ∧ ¬m = ↑x.1 ∧ (↑x.2 = m ∨ ↑x.2 ∈ neighbors_aux g ↑x.1)) =
--                              (fun (x: Fin (m + 1) × Fin (m + 1)) => ↑x.1 ∈ h ∧ ¬m = ↑x.1 ∧ (↑x.2 = m) ∨ ↑x.1 ∈ h ∧ ¬m = ↑x.1 ∧ ↑x.2 ∈ neighbors_aux g ↑x.1) := by
--                        ext; rename_i x
--                        tauto
--                      simp_rw [H]; clear H
--                      rw [Finset.filter_or]
--                      repeat rw [Finset.card_union]
--                      rw [<- Finset.filter_and]
--                      have H: (fun (a: Fin (m + 1) × Fin (m + 1)) => (↑a.1 ∈ h ∧ ¬m = ↑a.1 ∧ ↑a.2 = m) ∧ ↑a.1 ∈ h ∧ ¬m = ↑a.1 ∧ ↑a.2 ∈ neighbors_aux g ↑a.1) =
--                              (fun (a: Fin (m + 1) × Fin (m + 1)) => False) := by
--                        ext; rename_i x
--                        simp
--                        intros H1 H2 H3 H4 H5 H6
--                        have H7 := aux00 ↑x.1 ↑x.2 ⟨g, Hg3⟩
--                        simp at H7
--                        apply H7 at H6
--                        omega
--                      simp_rw [H, Finset.filter_False, Finset.card_empty]
--                      clear H
--                      simp
--                      simp_rw [finset_product_aux00 (fun x => m = ↑x) (fun x => ↑x ∈ h)]
--                      simp_rw [@Eq.comm _ m]
--                      rw [aux03]
--                      simp
--                      rw [aux04]
--                      . have H: ∀ (x y: Fin (m + 1)), ↑x ∈ h ∧ ¬ ↑x = m ∧ ↑y = m ↔
--                                ((fun x => ↑x ∈ h ∧ ¬ ↑x = m) x ∧ (fun y => ↑y = m) y) := by
--                          intros x y
--                          tauto
--                        simp_rw [H]
--                        simp_rw [finset_product_aux00 (fun x => ↑x ∈ h ∧ ¬ ↑x = m) (fun x => ↑x = m)]
--                        rw [aux03]
--                        . simp
--                          clear H
--                          have H: ∀ (x: Fin (m + 1)), ↑x ∈ h ∧ ¬ ↑x = m ↔ ↑x ∈ h := by
--                            intros x
--                            constructor <;> intro H0
--                            . tauto
--                            . have H1 := Hg2 _ H0
--                              constructor
--                              . tauto
--                              . omega
--                          simp_rw [H]
--                          rw [aux04]
--                          . clear H
--                            have H := finset_aux01 (fun (x: Fin (m + 1) × Fin (m + 1)) => ↑x.1 ∈ h) (fun x => ¬↑x.1 = m ∧ ↑x.2 ∈ neighbors_aux g ↑x.1)
--                            rw [Nat.add_assoc]
--                            rw [H]
--                            clear H
--                            have H: (fun (x: Fin (m + 1) × Fin (m + 1)) => ¬↑x.1 = m ∧ ↑x.2 ∈ neighbors_aux g ↑x.1) =
--                                    (fun (x: Fin (m + 1) × Fin (m + 1)) => ↑x.2 ∈ neighbors_aux g ↑x.1) := by
--                              ext; rename_i x
--                              constructor <;> intros H10
--                              . tauto
--                              . constructor
--                                . have aux := aux00 ↑x.1 ↑x.2 ⟨g, Hg3⟩
--                                  simp at aux
--                                  apply aux at H10
--                                  omega
--                                . assumption
--                            simp_rw [H]
--                            clear H
--                            have H: (Finset.filter (fun (x: Fin m × Fin m) ↦ ↑x.2 ∈ neighbors_aux g ↑x.1) Finset.univ).card =
--                                    (Finset.filter (fun (x: Fin (m + 1) × Fin (m + 1)) ↦ ↑x.2 ∈ neighbors_aux g ↑x.1) Finset.univ).card := by
--                              apply (finset_aux02 (fun x y => y ∈ neighbors_aux g x))
--                              intros x y H
--                              apply (aux00 x y ⟨g, Hg3⟩)
--                              simp
--                              assumption
--                            rw [H]
--                            omega
--                          . intros x Hx
--                            apply Hg2 at Hx
--                            omega
--                          . assumption
--                        . omega
--                      . intros x Hx
--                        apply Hg2 at Hx
--                        omega
--                      . assumption
--                      . omega
--                    . unfold Disjoint
--                      intros p H1 H2 H3 H4
--                      simp at *
--                      have H5 := H4
--                      apply H1 at H4
--                      apply H2 at H5
--                      simp at *
--                      tauto
--                  . unfold Disjoint
--                    intros p H1 H2 H3 H4
--                    simp at *
--                    have H5 := H4
--                    apply H1 at H4
--                    apply H2 at H5
--                    simp at *
--                    tauto

-- theorem sum_degrees_eq_twice_card_edges_Mathlib_version {V} (G: SimpleGraph V) [Fintype V] [DecidableRel G.Adj] [Fintype (Sym2 V)]:
--   ∑ v : V, G.degree v = 2 * G.edgeFinset.card := by
--   have equiv := Fintype.equivFin V
--   let G': SimpleGraph (Fin (Fintype.card V)) := by
--     refine (SimpleGraph.mk (fun v1 v2 => G.Adj (equiv.invFun v1) (equiv.invFun v2)) ?_ ?_)
--     . unfold Symmetric
--       intros x y
--       apply G.symm
--     . unfold Irreflexive
--       intros x
--       apply G.loopless
--   have H1: ∀ (v: V), v ∈ Finset.univ ↔ equiv v ∈ Finset.univ := by
--     intros v
--     constructor <;> intros H
--     . simp
--     . simp
--   have inst: ∀ v, Fintype ↑(G'.neighborSet (equiv v)) := by
--     intros x
--     unfold_let G'
--     simp
--     unfold SimpleGraph.neighborSet
--     simp
--     infer_instance
--   have H2: ∀ (x: V), G.degree x = G'.degree (equiv x) := by
--     intros x
--     unfold_let G'
--     simp
--     unfold SimpleGraph.degree
--     unfold SimpleGraph.neighborFinset
--     unfold SimpleGraph.neighborSet
--     simp
--     apply Finset.card_bij (fun x _ => equiv x)
--     . intros a Ha
--       simp at *
--       assumption
--     . simp at *
--     . simp
--       intros H2 H3
--       exists (equiv.symm H2)
--       simp
--       assumption
--   have H3: ∑ v, G.degree v = ∑ v, G'.degree v := by
--     apply (Fintype.sum_equiv equiv (fun x => G.degree x) (fun x => G'.degree x))
--     convert H2
--   rw [H3]
--   have H4: G.edgeFinset.card = G'.edgeFinset.card := by
--     unfold_let G'
--     unfold SimpleGraph.edgeFinset
--     unfold SimpleGraph.edgeSet
--     simp
--     apply Finset.card_bij (fun x _ => Sym2.map equiv x)
--     . intros a ha
--       simp at *
--       unfold SimpleGraph.edgeSet at *
--       unfold SimpleGraph.edgeSetEmbedding at *
--       simp at *
--       cases a
--       simp at *
--       exact ha
--     . intros a1 Ha1 a2 Ha2 H
--       cases a1
--       cases a2
--       simp at *
--       congr
--     . intros a Ha
--       cases a
--       rename_i x y
--       simp at *
--       exists s(equiv.symm x, equiv.symm y)
--       constructor
--       . unfold SimpleGraph.edgeSet
--         unfold SimpleGraph.edgeSetEmbedding
--         simp
--         exact Ha
--       . simp
--   rw [H4]
--   exact sum_degrees_eq_twice_card_edges_Fin_variant G'
