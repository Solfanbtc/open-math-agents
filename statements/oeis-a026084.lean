import Mathlib

/-!
# A026084: walks with first three steps ±1, later steps in {-1, 0, 1}, ending at 1

Source: https://oeis.org/A026084
Credit: @Solfanbtc

`a(n)` (offset 4) is the number of integer sequences `(s(0), …, s(n))` with `s(0) = 0`,
`|s(i) - s(i-1)| = 1` for `i = 1, 2, 3`, `|s(i) - s(i-1)| ≤ 1` for `i ≥ 4`, and `s(n) = 1`.
Such a sequence is determined by its steps `s(i) - s(i-1)`; below a step is `c - 1` for
`c : Fin 3`, steps `1, 2, 3` (indices `0, 1, 2` of `Fin n`) must be nonzero, and the steps must sum
to `1`. This reproduces all 26 data terms `3, 13, 33, 98, 278, …` (`n = 4, …, 29`).

Conjecture (R. J. Mathar, Jun 23 2013, OEIS formula):
`(n+1) a(n) + 3(-n+1) a(n-1) + (-n-9) a(n-2) + 3(n-5) a(n-3) = 0`.
Range: `n ≥ 7`, so that `a(n), …, a(n-3)` are all terms of the sequence (offset 4). Python: it
holds for `7 ≤ n < 60`. (With the counting definition extended below the offset it fails at
`n = 4`, which is outside the range.)
-/

namespace OMA.S_oeis_a026084

/-- The step value `c - 1 ∈ {-1, 0, 1}` encoded by `c : Fin 3`. -/
def step (c : Fin 3) : ℤ := (c : ℤ) - 1

/-- A026084: walks of length `n` from `0` to `1`, first three steps `±1`, others in `{-1,0,1}`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun d : Fin n → Fin 3 =>
    (∀ i : Fin n, (i : ℕ) < 3 → step (d i) ≠ 0) ∧ ∑ i, step (d i) = 1)).card

/-- Mathar's conjectured recurrence for A026084. -/
theorem main : ∀ n : ℕ, 7 ≤ n →
    ((n : ℤ) + 1) * a n + 3 * (-(n : ℤ) + 1) * a (n - 1) + (-(n : ℤ) - 9) * a (n - 2)
      + 3 * ((n : ℤ) - 5) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a026084
