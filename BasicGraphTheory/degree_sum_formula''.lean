import BasicGraphTheory.degree_sum_formula
import BasicGraphTheory.relation_to_SimpleGraph

-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/DegreeSum.html#SimpleGraph.two_mul_card_edgeFinset
theorem two_mul_card_edgeFinset {V} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] [Fintype (Sym2 V)]:
  2 * G.edgeFinset.card = (Finset.filter (fun (x: V × V) => G.Adj x.1 x.2) Finset.univ).card := by sorry

theorem sum_degrees_eq_twice_card_edges_Fin_variant {n} (G: SimpleGraph (Fin n)) [DecidableRel G.Adj]:
  ∑ v, G.degree v = 2 * G.edgeFinset.card := by
  simp_rw [degree_conserved]
  have H := sum_of_degrees_twice_of_edges (SimpleGraph_to_simple_graph G)
  rw [@Finset.sum_range] at H
  rw [H]
  clear H
  rw [two_mul_card_edgeFinset]
  simp_rw [adj_preserved_SG_to_sg]
  --
  generalize (SimpleGraph_to_simple_graph G) = W
  rename_i inst; clear inst G
  cases W; rename_i g Hg
  induction n with
  | zero => cases g
            simp at *
            unfold edges edges_aux
            simp
  | succ m iH => cases g
                 rename_i h g
                 unfold edges edges_aux
                 simp
                 obtain ⟨Hg1, Hg2, Hg3⟩ := Hg
                 have H := iH g Hg3
                 unfold edges at H
                 simp at H
                 have H0: 2 * ((edges_aux g).length + h.length) = 2 * (edges_aux g).length + 2 * h.length := by
                   omega
                 rw [H0, H]
                 unfold adjacent neighbors
                 simp_rw [neighbors_aux]
                 have H1: ∀ x: Fin (m + 1) × Fin (m + 1), (↑x.2 ∈
                          if m = ↑x.1 then h ++ neighbors_aux g ↑x.1
                          else if ↑x.1 ∈ h then m :: neighbors_aux g ↑x.1 else neighbors_aux g ↑x.1) ↔
                          (if m = ↑x.1 then ↑x.2 ∈ h ++ neighbors_aux g ↑x.1 else
                           if ↑x.1 ∈ h then ↑x.2 ∈ m :: neighbors_aux g ↑x.1 else
                           ↑x.2 ∈ neighbors_aux g ↑x.1) := by
                   intros p
                   split_ifs <;> tauto
                 simp_rw [H1]
                 clear iH H1 H H0
                 simp
                 repeat rw [finset_filter_ite]
                 rw [Finset.card_union_of_disjoint]
                 . have H: ∀ (x: Fin (m + 1) × Fin (m + 1)),
                           (¬m = ↑x.1 ∧ if ↑x.1 ∈ h then ↑x.2 = m ∨ ↑x.2 ∈ neighbors_aux g ↑x.1 else ↑x.2 ∈ neighbors_aux g ↑x.1) ↔
                           (if ↑x.1 ∈ h then ¬ m = ↑x.1 ∧ (↑x.2 = m ∨ ↑x.2 ∈ neighbors_aux g ↑x.1) else ¬ m = ↑x.1 ∧ ↑x.2 ∈ neighbors_aux g ↑x.1) := by
                     intros x
                     split_ifs <;> tauto
                   simp_rw [H]
                   clear H
                   rw [finset_filter_ite]
                   rw [Finset.card_union_of_disjoint]
                   . have H: (fun (x: Fin (m + 1) × Fin (m + 1)) => m = ↑x.1 ∧ (↑x.2 ∈ h ∨ ↑x.2 ∈ neighbors_aux g ↑x.1)) =
                             (fun (x: Fin (m + 1) × Fin (m + 1)) => m = ↑x.1 ∧ ↑x.2 ∈ h) := by
                       ext; rename_i x
                       constructor <;> intros H
                       . obtain ⟨H1, H2⟩ := H
                         rw [<- H1] at H2
                         obtain H2 | H2 := H2
                         . tauto
                         . have H3 := size_limit_on_adjacent_nodes m ↑x.2 ⟨g, Hg3⟩
                           unfold adjacent neighbors at H3
                           apply H3 at H2
                           omega
                       . tauto
                     simp_rw [H]
                     clear H
                     have H: (fun (x: Fin (m + 1) × Fin (m + 1)) => ↑x.1 ∈ h ∧ ¬m = ↑x.1 ∧ (↑x.2 = m ∨ ↑x.2 ∈ neighbors_aux g ↑x.1)) =
                             (fun (x: Fin (m + 1) × Fin (m + 1)) => ↑x.1 ∈ h ∧ ¬m = ↑x.1 ∧ (↑x.2 = m) ∨ ↑x.1 ∈ h ∧ ¬m = ↑x.1 ∧ ↑x.2 ∈ neighbors_aux g ↑x.1) := by
                       ext; rename_i x
                       tauto
                     simp_rw [H]; clear H
                     rw [Finset.filter_or]
                     repeat rw [Finset.card_union]
                     rw [<- Finset.filter_and]
                     have H: (fun (a: Fin (m + 1) × Fin (m + 1)) => (↑a.1 ∈ h ∧ ¬m = ↑a.1 ∧ ↑a.2 = m) ∧ ↑a.1 ∈ h ∧ ¬m = ↑a.1 ∧ ↑a.2 ∈ neighbors_aux g ↑a.1) =
                             (fun (a: Fin (m + 1) × Fin (m + 1)) => False) := by
                       ext; rename_i x
                       simp
                       intros H1 H2 H3 H4 H5 H6
                       have H7 := size_limit_on_adjacent_nodes ↑x.1 ↑x.2 ⟨g, Hg3⟩
                       unfold adjacent neighbors at H7
                       apply H7 at H6
                       omega
                     simp_rw [H, Finset.filter_False, Finset.card_empty]
                     clear H
                     simp
                     simp_rw [aux06 (fun x => m = ↑x) (fun x => ↑x ∈ h)]
                     simp_rw [@Eq.comm _ m]
                     rw [aux01]
                     simp
                     have Hg2': ∀ x ∈ h, x < m + 1 := by
                       intros x Hx
                       apply Hg2 at Hx
                       omega
                     have H: (Finset.filter (fun (x: Fin (m + 1)) ↦ ↑x ∈ h) Finset.univ).card = h.length := by
                       have aux := aux02 _ h Hg2' Hg1
                       convert aux
                     rw [H]; clear H
                     . have H: ∀ (x y: Fin (m + 1)), ↑x ∈ h ∧ ¬ ↑x = m ∧ ↑y = m ↔
                               ((fun x => ↑x ∈ h ∧ ¬ ↑x = m) x ∧ (fun y => ↑y = m) y) := by
                         intros x y
                         tauto
                       simp_rw [H]; clear H
                       simp_rw [aux06 (fun x => ↑x ∈ h ∧ ¬ ↑x = m) (fun x => ↑x = m)]
                       rw [aux01]
                       . simp
                         have H: ∀ (x: Fin (m + 1)), ↑x ∈ h ∧ ¬ ↑x = m ↔ ↑x ∈ h := by
                           intros x
                           constructor <;> intro H0
                           . tauto
                           . have H1 := Hg2 _ H0
                             constructor
                             . tauto
                             . omega
                         simp_rw [H]; clear H
                         have H: (Finset.filter (fun (x: Fin (m + 1)) ↦ ↑x ∈ h) Finset.univ).card = h.length := by
                           have aux := aux02 _ h Hg2' Hg1
                           convert aux
                         rw [H]; clear H
                         have H := aux07 (fun (x: Fin (m + 1) × Fin (m + 1)) => ↑x.1 ∈ h) (fun x => ¬↑x.1 = m ∧ ↑x.2 ∈ neighbors_aux g ↑x.1)
                         rw [Nat.add_assoc, H]
                         clear H
                         have H: (fun (x: Fin (m + 1) × Fin (m + 1)) => ¬↑x.1 = m ∧ ↑x.2 ∈ neighbors_aux g ↑x.1) =
                                 (fun (x: Fin (m + 1) × Fin (m + 1)) => ↑x.2 ∈ neighbors_aux g ↑x.1) := by
                           ext; rename_i x
                           constructor <;> intros H10
                           . tauto
                           . constructor
                             . have aux := size_limit_on_adjacent_nodes ↑x.1 ↑x.2 ⟨g, Hg3⟩
                               unfold adjacent neighbors at aux
                               apply aux at H10
                               omega
                             . assumption
                         simp_rw [H]
                         clear H
                         have H: (Finset.filter (fun (x: Fin m × Fin m) ↦ ↑x.2 ∈ neighbors_aux g ↑x.1) Finset.univ).card =
                                 (Finset.filter (fun (x: Fin (m + 1) × Fin (m + 1)) ↦ ↑x.2 ∈ neighbors_aux g ↑x.1) Finset.univ).card := by
                           apply (aux08 (fun x y => y ∈ neighbors_aux g x))
                           intros x y H
                           apply (size_limit_on_adjacent_nodes x y ⟨g, Hg3⟩)
                           assumption
                         rw [H]
                         omega
                       . omega
                     . omega
                   . unfold Disjoint
                     intros p H1 H2 H3 H4
                     simp at *
                     have H5 := H4
                     apply H1 at H4
                     apply H2 at H5
                     simp at *
                     tauto
                 . unfold Disjoint
                   intros p H1 H2 H3 H4
                   simp at *
                   have H5 := H4
                   apply H1 at H4
                   apply H2 at H5
                   simp at *
                   tauto

theorem sum_degrees_eq_twice_card_edges_Mathlib_version {V} (G: SimpleGraph V) [Fintype V] [DecidableRel G.Adj] [Fintype (Sym2 V)]:
  ∑ v : V, G.degree v = 2 * G.edgeFinset.card := by
  have equiv := Fintype.equivFin V
  let G': SimpleGraph (Fin (Fintype.card V)) := by
    refine (SimpleGraph.mk (fun v1 v2 => G.Adj (equiv.invFun v1) (equiv.invFun v2)) ?_ ?_)
    . intros x y
      apply G.symm
    . intros x
      apply G.loopless
  have H1: ∀ (v: V), v ∈ Finset.univ ↔ equiv v ∈ Finset.univ := by
    intros v
    constructor <;> simp
  have inst: ∀ v, Fintype ↑(G'.neighborSet (equiv v)) := by
    intros x
    unfold_let G'
    unfold SimpleGraph.neighborSet
    simp
    infer_instance
  have H2: ∀ (x: V), G.degree x = G'.degree (equiv x) := by
    intros x
    unfold_let G'
    unfold SimpleGraph.degree SimpleGraph.neighborFinset SimpleGraph.neighborSet
    simp
    apply Finset.card_bij (fun x _ => equiv x)
    . intros a Ha
      simp at *
      assumption
    . simp at *
    . simp
      intros H2 H3
      exists (equiv.symm H2)
      simp
      assumption
  have H3: ∑ v, G.degree v = ∑ v, G'.degree v := by
    apply (Fintype.sum_equiv equiv (fun x => G.degree x) (fun x => G'.degree x))
    convert H2
  rw [H3]
  have H4: G.edgeFinset.card = G'.edgeFinset.card := by
    unfold_let G'
    unfold SimpleGraph.edgeFinset SimpleGraph.edgeSet
    simp
    apply Finset.card_bij (fun x _ => Sym2.map equiv x)
    . intros a ha
      simp at *
      unfold SimpleGraph.edgeSet SimpleGraph.edgeSetEmbedding at *
      cases a
      simp at *
      exact ha
    . intros a1 Ha1 a2 Ha2 H
      cases a1
      cases a2
      simp at *
      congr
    . intros a Ha
      cases a
      rename_i x y
      simp at *
      exists s(equiv.symm x, equiv.symm y)
      constructor
      . unfold SimpleGraph.edgeSet SimpleGraph.edgeSetEmbedding
        simp
        exact Ha
      . simp
  rw [H4]
  exact sum_degrees_eq_twice_card_edges_Fin_variant G'
