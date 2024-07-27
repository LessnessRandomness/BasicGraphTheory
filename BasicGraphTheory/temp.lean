import Mathlib

theorem T0 {V} (G: SimpleGraph V) [Fintype V] [DecidableRel G.Adj]:
  ∑ v, G.degree v = 2 * G.edgeFinset.card := by
  have H: exists W, W = Fintype.card V := by
    exists (Fintype.card V)
  cases H; rename_i W Hw
  induction W with
  | zero => rw [Eq.comm, Fintype.card_eq_zero_iff] at Hw
            rw [Fintype.sum_empty]
            have H: G = ⊥ := by
              ext
              simp
              intros H
              cases Hw; rename_i x empty
              exact (empty x)
            cases H
            simp
  | succ m iH => simp
                 have H: V ≃ Fin (m + 1) := by
                   rw [Hw]
                   apply Fintype.equivFin
                 cases H
                 rename_i toFun invFun left_inv right_inv

                 sorry
