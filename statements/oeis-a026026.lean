import Mathlib

/-!
# A026026: nonnegative ±1 walks from 3 to 4

Source: https://oeis.org/A026026
Credit: @Solfanbtc

The entry's name: `a(n)` is the number of `(s(0), …, s(2n-1))` with every `s(i)` a nonnegative
integer, `|s(i) - s(i-1)| = 1`, `s(0) = 3`, `s(2n-1) = 4`; data (offset 2):
`1, 3, 10, 35, 125, 451, …`.

Offset: the name's count for index `m` (walks with `2m - 1` steps) equals the data term of index
`m + 1` (it gives `1, 3, 10, 35, …` for `m = 1, 2, 3, 4, …`), i.e. the name is written for offset
1, while the data, the g.f. `x^2 (1 + x^2 C^4) C^3` and Krause's formula
`a(n) = binom(2n-3, n-2) - binom(2n-3, n-6)` use offset 2. We follow the OEIS offset 2, which is
the indexing of Mathar's recurrence (it is fitted to the data): `a(n)` is the number of
nonnegative walks with `2n - 3` steps `±1` from `3` to `4`. This reproduces all 26 data terms
and agrees with Krause's formula for `n < 70`.

Conjecture (R. J. Mathar, Jun 22 2013, OEIS formula):
`-(n+3)(11n-38) a(n) + 2(35n^2 - 86n - 102) a(n-1) - 4(13n-30)(2n-5) a(n-2) = 0`.
Range: `n ≥ 4`, so that `a(n), a(n-1), a(n-2)` are terms (offset 2). Python: holds for
`4 ≤ n < 70`.
-/

namespace OMA.S_oeis_a026026

/-- The step `+1` (`true`) or `-1` (`false`). -/
def step (b : Bool) : ℤ := if b then 1 else -1

/-- Position after the first `k` steps of the walk `d` started at `3`. -/
def pos {L : ℕ} (d : Fin L → Bool) (k : ℕ) : ℤ :=
  3 + ∑ i : Fin L, if (i : ℕ) < k then step (d i) else 0

/-- A026026 (offset 2): nonnegative walks with `2n - 3` steps `±1` from `3` to `4`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun d : Fin (2 * n - 3) → Bool =>
    (∀ k ≤ 2 * n - 3, 0 ≤ pos d k) ∧ pos d (2 * n - 3) = 4)).card

/-- Mathar's conjectured recurrence for A026026. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    -((n : ℤ) + 3) * (11 * n - 38) * a n + 2 * (35 * (n : ℤ) ^ 2 - 86 * n - 102) * a (n - 1)
      - 4 * (13 * (n : ℤ) - 30) * (2 * n - 5) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a026026
