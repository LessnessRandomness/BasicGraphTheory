import Mathlib.Tactic.Tauto
import Mathlib
-- How to import specifically Mathlib.Combinatorics.SimpleGraph?

def CompleteGraph (n: Nat): SimpleGraph (Fin n) := by
  refine (SimpleGraph.mk (λ x y => x ≠ y) ?_ ?_)
  . unfold Symmetric
    simp
    tauto
  . unfold Irreflexive
    simp

def CycleGraph (n: Nat): SimpleGraph (Fin n) := by
  refine (SimpleGraph.mk (λ x y => y = x + 1) ?_ ?_)
  .
    sorry
  . sorry
