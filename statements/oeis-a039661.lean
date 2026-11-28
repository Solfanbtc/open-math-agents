import Mathlib

/-!
# A039661: Decimal expansion of exp(Pi).

Source: https://oeis.org/A039661
Credit: @Solfanbtc

Conjecture (Simon Plouffe, Sep 09 2025, in the entry's formulas; also recorded as "Empirical" in
A132136): `exp(π) = ∑_{k ≥ 0} A132136(k) / exp(k π)`.

A132136 (offset 1) is the expansion of `-λ(t + 1) = λ/(1 - λ)` in powers of the nome
`q = exp(π i t)`, with g.f. `16 x ∏_{k > 0} ((1 + x^{2k}) / (1 - x^{2k-1}))^8`:
`16, 128, 704, 3072, 11488, ...`. The `k = 0` term is `0` (the g.f. has no constant term;
A132136 has no term of index 0), so the series is `∑_{k ≥ 1} A132136(k) e^{-kπ}`.

WARNING: the claim appears to be FALSE. At `q = e^{-π}` (`t = i`) the modular lambda function is
`λ(i) = 1/2`, so the series should sum to `λ/(1 - λ) = 1`, not `e^π ≈ 23.14`. A python3 check
(exact integer coefficients from the product formula, 50-digit arithmetic, 299 terms) gives the
sum `1.000000000...` (50 digits). The claim is stated here exactly as written, so that it can be
disproved (`OMA.disproof`); the entry does not record a refutation.

Conventions:
* `A132136(n)` for `n ≥ 1` is `16 · [x^{n-1}] ∏_{k ≥ 1} (1 + x^{2k})^8 (1 - x^{2k-1})^{-8}`; the
  coefficient of `x^{n-1}` only depends on the factors with `2k - 1 ≤ n`, so the product is
  truncated to `k ≤ n` (each further factor is `1 + O(x^{n+1})`). `1/(1 - x^m)` is the series
  `∑_j x^{mj}`. A132136(0) := 0. The python3 computation of this product reproduces the data.
* The terms are nonnegative, so the sum is an honest `HasSum`.
-/

namespace OMA.S_oeis_a039661

open PowerSeries

/-- `1 / (1 - x^m)` as a power series. -/
def geom (m : ℕ) : ℤ⟦X⟧ := mk fun j => if m ∣ j then 1 else 0

/-- `∏_{k=1}^{K} (1 + x^{2k})^8 / (1 - x^{2k-1})^8`. -/
noncomputable def prodTrunc (K : ℕ) : ℤ⟦X⟧ :=
  ∏ k ∈ Finset.Icc 1 K, (1 + X ^ (2 * k)) ^ 8 * geom (2 * k - 1) ^ 8

/-- `A132136(n)` (`n ≥ 1`), with `A132136(0) = 0`. -/
noncomputable def A132136 (n : ℕ) : ℤ := if n = 0 then 0 else 16 * coeff (n - 1) (prodTrunc n)

/-- Plouffe's conjecture: `exp(π) = ∑_{k ≥ 0} A132136(k) / exp(kπ)` (apparently false: the sum
is `1`). -/
theorem main :
    HasSum (fun k : ℕ => (A132136 k : ℝ) / Real.exp (k * Real.pi)) (Real.exp Real.pi) := by
  sorry

end OMA.S_oeis_a039661
