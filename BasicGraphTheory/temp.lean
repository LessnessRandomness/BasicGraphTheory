import Mathlib

theorem Unnamed (a: ℕ → ℝ) (h0: a 0 = 1/2) (n: ℕ) (Hn: n > 1) (ha : ∀ k: ℕ, a (k+1) = a k + (a k) ^ 2 / n): ∀ m, a m > 0 := by
  intro m
  induction m with
  | zero => linarith
  | succ m' iH => rw [ha]
                  positivity

theorem Goal (a: ℕ → ℝ) (h0: a 0 = 1/2) (n: ℕ) (Hn: n > 1) (ha : ∀ k: ℕ, a (k+1) = a k + (a k) ^ 2 / n): a n > 0 :=
  Unnamed a h0 n Hn ha n
