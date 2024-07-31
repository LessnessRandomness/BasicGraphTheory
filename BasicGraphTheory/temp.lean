import Mathlib

theorem sum_degrees_eq_twice_card_edges_Fin_variant {n} (G: SimpleGraph (Fin n)) [DecidableRel G.Adj]:
  ∑ v, G.degree v = 2 * G.edgeFinset.card := by sorry

theorem sum_degrees_eq_twice_card_edges_Mathlib_version {V} (G: SimpleGraph V) [Fintype V] [DecidableRel G.Adj] [Fintype (Sym2 V)]:
  ∑ v : V, G.degree v = 2 * G.edgeFinset.card := by
  have equiv := Fintype.equivFin V
  let G': SimpleGraph (Fin (Fintype.card V)) := by
    refine (SimpleGraph.mk (fun v1 v2 => G.Adj (equiv.invFun v1) (equiv.invFun v2)) ?_ ?_)
    . unfold Symmetric
      intros x y
      apply G.symm
    . unfold Irreflexive
      intros x
      apply G.loopless
  have H1: ∀ (v: V), v ∈ Finset.univ ↔ equiv v ∈ Finset.univ := by sorry
  have inst: ∀ v, Fintype ↑(G'.neighborSet (equiv v)) := by sorry
  have H2: ∀ (x: V), G.degree x = G'.degree (equiv x) := by sorry
  have H3: ∑ v, G.degree v = ∑ v, G'.degree v := by
    apply (Fintype.sum_equiv equiv (fun x => G.degree x) (fun x => G'.degree x))
    #check H2
    -- exact H2 fails
    exact H2
    sorry
  sorry
