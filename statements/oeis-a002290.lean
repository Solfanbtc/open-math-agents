import Mathlib

/-!
# A002290: Absolute value of Glaisher's alpha(n).

Source: https://oeis.org/A002290
Credit: @Solfanbtc

`a(n) = |A225543(n)|` (offset 0), the absolute values of the coefficients of
`(η(q²)⁶ / (η(q) η(q⁴)²))⁴`, with `η(q) = ∏_{k ≥ 1} (1 - q^k)` as in the entry's PARI and
Mathematica programs: `1, 4, 10, 56, 29, 332, 30, 1064, ...`.

Conjecture (Vaclav Kotesovec, Sep 25 2026, in the entry): `∑_{k=1}^{n} a(k)² ~ c · n⁶`, where
`c = 2.19...`. Stated as: there is `c` with `2.19 ≤ c < 2.20` and
`(∑_{k=1}^{n} a(k)²) / n⁶ → c`.

A python3 check: the product formula reproduces all 46 data terms; the ratio
`(∑_{k ≤ n} a(k)²)/n⁶` is `2.147, 2.354, 2.166, 2.236` at `n = 500, 1000, 2000, 2999`
(it oscillates, roughly around 2.2).

Conventions:
* The series is `∏_{k ≥ 1} (1 - x^{2k})^{24} (1 - x^k)^{-4} (1 - x^{4k})^{-8}`; its coefficient of
  `xⁿ` only depends on the factors with `k ≤ n`, so the product is truncated to `k ≤ n`.
  `1/(1 - x^m)` is the series `∑_j x^{mj}`.
* "`c = 2.19...`" is read as `c ∈ [2.19, 2.20)`.
-/

namespace OMA.S_oeis_a002290

open PowerSeries Filter Topology

/-- `1 / (1 - x^m)` as a power series. -/
def geom (m : ℕ) : ℤ⟦X⟧ := mk fun j => if m ∣ j then 1 else 0

/-- `∏_{k=1}^{K} (1 - x^{2k})^{24} (1 - x^k)^{-4} (1 - x^{4k})^{-8}`. -/
noncomputable def prodTrunc (K : ℕ) : ℤ⟦X⟧ :=
  ∏ k ∈ Finset.Icc 1 K, (1 - X ^ (2 * k)) ^ 24 * geom k ^ 4 * geom (4 * k) ^ 8

/-- `a n = A002290(n) = |A225543(n)|`. -/
noncomputable def a (n : ℕ) : ℕ := (coeff n (prodTrunc n)).natAbs

/-- Kotesovec's conjecture: `∑_{k=1}^{n} a(k)² ~ c n⁶` with `c = 2.19...`. -/
theorem main : ∃ c : ℝ, 2.19 ≤ c ∧ c < 2.20 ∧
    Tendsto (fun n : ℕ => ((∑ k ∈ Finset.Icc 1 n, (a k : ℝ) ^ 2)) / (n : ℝ) ^ 6) atTop (𝓝 c) := by
  sorry

end OMA.S_oeis_a002290
