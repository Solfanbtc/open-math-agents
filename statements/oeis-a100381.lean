import Mathlib

/-!
# A100381: a(n) = 2^n*binomial(n,2).

Source: https://oeis.org/A100381
Credit: @Solfanbtc

Claims (Peter Bala, Mar 04 2024, %F lines of A100381), with `a(n) = 2^n * binomial(n, 2)`:
1. `Sum_{k=2..n+2} 1/a(k) = 1/(4 - 4/(7 - 12/(10 - ... - 2n(n+1)/(3n+4))))`;
2. `Sum_{k=2..n+2} (-1)^k/a(k) = 1/(4 + 4/(5 + 12/(6 + ... + 2n(n+1)/(n+4))))`;
3. letting `n → ∞`: `1 - log 2 = Sum_{k ≥ 2} 1/a(k) = 1/(4 - 4/(7 - 12/(10 - ...)))`
   (an equivalent continued fraction for `1 - log 2` was conjectured by the Ramanujan Machine) and
   `3 log(3/2) - 1 = Sum_{k ≥ 2} (-1)^k/a(k) = 1/(4 + 4/(5 + 12/(6 + ...)))`.
The two series values are also recorded in the entry (G. McRae 2006; A. Eldar 2020; cf. Jolley,
Summation of Series, eq. (214)). These are stated as known results; the statement below
records all of them.

Formalization.
* The `k`-th level (`k = 0, 1, ..., n`) of the first continued fraction has denominator
  `3k + 4` and, below it, partial numerator `2(k+1)(k+2)` (`4, 12, 24, ...`); the last level
  `k = n` is just `3n + 4`. `cf1Tail k len` is the value of the levels `k, ..., k + len`,
  so the `n`-th finite continued fraction is `1 / cf1Tail 0 n`. Likewise `cf2Tail` with
  denominators `k + 4` and `+` signs.
* The infinite continued fractions are read as limits of these finite ones, as in the source
  ("letting n → ∞ in the above"). The finite identities are stated in `ℚ` (division by `0`
  never occurs: python3 checks all levels for `n < 40`), the series and limits in `ℝ`.

Checked with python3 (exact fractions): identities 1 and 2 hold for `0 ≤ n < 40`, and the
finite continued fractions at `n = 39` agree with `1 - log 2` and `3 log(3/2) - 1` to 15 digits.
-/

namespace OMA.S_oeis_a100381

open Filter Topology Finset

/-- A100381: `a(n) = 2^n * binomial(n, 2)`. -/
def a (n : ℕ) : ℕ := 2 ^ n * n.choose 2

/-- Levels `k, ..., k + len` of `4 - 4/(7 - 12/(10 - ... - 2n(n+1)/(3n+4)))`. -/
def cf1Tail (k : ℕ) : ℕ → ℚ
  | 0 => 3 * k + 4
  | len + 1 => (3 * k + 4) - (2 * (k + 1) * (k + 2) : ℚ) / cf1Tail (k + 1) len

/-- Levels `k, ..., k + len` of `4 + 4/(5 + 12/(6 + ... + 2n(n+1)/(n+4)))`. -/
def cf2Tail (k : ℕ) : ℕ → ℚ
  | 0 => k + 4
  | len + 1 => (k + 4) + (2 * (k + 1) * (k + 2) : ℚ) / cf2Tail (k + 1) len

/-- Bala's finite continued-fraction identities and their limits. -/
theorem main :
    (∀ n : ℕ, ∑ k ∈ Icc 2 (n + 2), (1 : ℚ) / a k = 1 / cf1Tail 0 n) ∧
    (∀ n : ℕ, ∑ k ∈ Icc 2 (n + 2), ((-1 : ℚ) ^ k) / a k = 1 / cf2Tail 0 n) ∧
    HasSum (fun k : ℕ => (1 : ℝ) / a (k + 2)) (1 - Real.log 2) ∧
    HasSum (fun k : ℕ => ((-1 : ℝ) ^ (k + 2)) / a (k + 2)) (3 * Real.log (3 / 2) - 1) ∧
    Tendsto (fun n : ℕ => ((1 / cf1Tail 0 n : ℚ) : ℝ)) atTop (𝓝 (1 - Real.log 2)) ∧
    Tendsto (fun n : ℕ => ((1 / cf2Tail 0 n : ℚ) : ℝ)) atTop
      (𝓝 (3 * Real.log (3 / 2) - 1)) := by
  sorry

end OMA.S_oeis_a100381
