import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Finset BigOperators

/-- The one-step estimate behind the note. `e p` is the mass of block `p` (q blocks),
`x0` the mass of the empty body, `v0` the empty-body mass after one step, bounded below
by the pairs that produce the empty body with probability one. -/
theorem xi_qso_step (q : ℕ) (hq : 0 < q) (e : Fin q → ℝ) (x0 v0 : ℝ)
    (hsum : x0 + ∑ p, e p = 1)
    (hv : x0 ^ 2 + 2 * x0 * (1 - x0) + ∑ p, e p ^ 2 ≤ v0) :
    1 - v0 ≤ (1 - 1 / (q : ℝ)) * (1 - x0) ^ 2 := by
  have hy : ∑ p, e p = 1 - x0 := by linarith
  have hcs : (∑ p, e p) ^ 2 ≤ (q : ℝ) * ∑ p, e p ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin q))) (f := e)
    simpa using this
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hlow : (1 - x0) ^ 2 / q ≤ ∑ p, e p ^ 2 := by
    rw [div_le_iff₀ hqpos, ← hy]; linarith
  have key : 1 - v0 ≤ (1 - x0) ^ 2 - (1 - x0) ^ 2 / q := by nlinarith
  have : (1 - 1 / (q : ℝ)) * (1 - x0) ^ 2 = (1 - x0) ^ 2 - (1 - x0) ^ 2 / q := by
    field_simp
  linarith

/-- Iterating `y (n+1) ≤ c * y n ^ 2` with `0 ≤ y n ≤ 1` and `0 ≤ c ≤ 1` gives `y n ≤ c ^ n * y 0`. -/
theorem xi_qso_iter (c : ℝ) (hc0 : 0 ≤ c) (y : ℕ → ℝ) (hy0 : ∀ n, 0 ≤ y n) (hy1 : ∀ n, y n ≤ 1)
    (hstep : ∀ n, y (n + 1) ≤ c * y n ^ 2) : ∀ n, y n ≤ c ^ n * y 0 := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    have h1 : y (k + 1) ≤ c * y k := by
      have : y k ^ 2 ≤ y k := by nlinarith [hy0 k, hy1 k]
      nlinarith [hstep k, hc0]
    calc y (k + 1) ≤ c * y k := h1
      _ ≤ c * (c ^ k * y 0) := by exact mul_le_mul_of_nonneg_left ih hc0
      _ = c ^ (k + 1) * y 0 := by ring

/-- A fixed point has zero off-empty mass when `c < 1`. -/
theorem xi_qso_fixed (c y : ℝ) (hc0 : 0 ≤ c) (hc : c < 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (h : y ≤ c * y ^ 2) : y = 0 := by
  by_contra hne
  have hpos : 0 < y := lt_of_le_of_ne hy0 (Ne.symm hne)
  have hsq : y ^ 2 ≤ y := by nlinarith
  have h2 : c * y ^ 2 ≤ c * y := mul_le_mul_of_nonneg_left hsq hc0
  have h3 : 0 < y * (1 - c) := mul_pos hpos (by linarith)
  nlinarith
