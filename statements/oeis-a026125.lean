import Mathlib

/-!
# A026125: nonnegative walks from 1 to 4, first step ±1, later steps in {-1, 0, 1}

Source: https://oeis.org/A026125
Credit: @Solfanbtc

`a(n)` (offset 3) is the number of `(s(0), …, s(n))` with every `s(i)` a nonnegative integer,
`s(0) = 1`, `s(n) = 4`, `|s(1) - s(0)| = 1` and `|s(i) - s(i-1)| ≤ 1` for `i ≥ 2`. Such a string
is determined by its steps; below a step is `c - 1` for `c : Fin 3`, the first step (index `0`)
must be nonzero, and every position `s(k) = 1 + (sum of the first k steps)`, `0 ≤ k ≤ n`, must be
`≥ 0`. This reproduces all 27 data terms `1, 3, 11, 35, 110, …` (`n = 3, …, 29`).

Conjecture (R. J. Mathar, Jun 23 2013, OEIS formula):
`-(n+7)(n-3) a(n) + (4n+17)(n-3) a(n-1) + (-2n^2 + 13n + 27) a(n-2) - (4n+5)(n-3) a(n-3)
 + 3(n-3)(n-4) a(n-4) = 0`.
Range: `n ≥ 7`, so that `a(n), …, a(n-4)` are all terms (offset 3). Python: holds for
`7 ≤ n < 60`.
-/

namespace OMA.S_oeis_a026125

/-- The step value `c - 1 ∈ {-1, 0, 1}` encoded by `c : Fin 3`. -/
def step (c : Fin 3) : ℤ := (c : ℤ) - 1

/-- Position `s(k)` after the first `k` steps, starting from `s(0) = 1`. -/
def pos {n : ℕ} (d : Fin n → Fin 3) (k : ℕ) : ℤ :=
  1 + ∑ i : Fin n, if (i : ℕ) < k then step (d i) else 0

/-- A026125: nonnegative strings from `1` to `4` of length `n`, first step `±1`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun d : Fin n → Fin 3 =>
    (∀ i : Fin n, (i : ℕ) = 0 → step (d i) ≠ 0) ∧ (∀ k ≤ n, 0 ≤ pos d k) ∧ pos d n = 4)).card

/-- Mathar's conjectured recurrence for A026125. -/
theorem main : ∀ n : ℕ, 7 ≤ n →
    -((n : ℤ) + 7) * (n - 3) * a n + (4 * (n : ℤ) + 17) * (n - 3) * a (n - 1)
      + (-2 * (n : ℤ) ^ 2 + 13 * n + 27) * a (n - 2) - (4 * (n : ℤ) + 5) * (n - 3) * a (n - 3)
      + 3 * ((n : ℤ) - 3) * (n - 4) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a026125
