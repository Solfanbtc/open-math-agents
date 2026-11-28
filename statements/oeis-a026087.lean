import Mathlib

/-!
# A026087: walks with first three steps ±1, later steps in {-1, 0, 1}, ending at 4

Source: https://oeis.org/A026087
Credit: @Solfanbtc

`a(n)` (offset 4) is the number of integer sequences `(s(0), …, s(n))` with `s(0) = 0`,
`|s(i) - s(i-1)| = 1` for `i = 1, 2, 3`, `|s(i) - s(i-1)| ≤ 1` for `i ≥ 4`, and `s(n) = 4`.
Such a sequence is determined by its steps `s(i) - s(i-1)`; below a step is `c - 1` for
`c : Fin 3`, steps `1, 2, 3` (indices `0, 1, 2` of `Fin n`) must be nonzero, and the steps must sum
to `4`. This reproduces all 27 data terms `1, 2, 9, 28, 93, …` (`n = 4, …, 30`).

Conjecture (R. J. Mathar, Jun 23 2013, OEIS formula):
`-(n-4)(n+4) a(n) + (4n^2 - 11n - 27) a(n-1) + (-2n^2 + 29n - 24) a(n-2)
 - (4n+5)(n-5) a(n-3) + 3(n-5)(n-6) a(n-4) = 0`.
Range: `n ≥ 8`, so that `a(n), …, a(n-4)` are all terms of the sequence (offset 4). (Python: it
holds for `8 ≤ n < 60`; with the counting definition, for which `a(n) = 0` when `n < 4`, it also
holds for `4 ≤ n < 8`.)
-/

namespace OMA.S_oeis_a026087

/-- The step value `c - 1 ∈ {-1, 0, 1}` encoded by `c : Fin 3`. -/
def step (c : Fin 3) : ℤ := (c : ℤ) - 1

/-- A026087: walks of length `n` from `0` to `4`, first three steps `±1`, others in `{-1,0,1}`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun d : Fin n → Fin 3 =>
    (∀ i : Fin n, (i : ℕ) < 3 → step (d i) ≠ 0) ∧ ∑ i, step (d i) = 4)).card

/-- Mathar's conjectured recurrence for A026087. -/
theorem main : ∀ n : ℕ, 8 ≤ n →
    -((n : ℤ) - 4) * (n + 4) * a n + (4 * (n : ℤ) ^ 2 - 11 * n - 27) * a (n - 1)
      + (-2 * (n : ℤ) ^ 2 + 29 * n - 24) * a (n - 2) - (4 * (n : ℤ) + 5) * (n - 5) * a (n - 3)
      + 3 * ((n : ℤ) - 5) * (n - 6) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a026087
