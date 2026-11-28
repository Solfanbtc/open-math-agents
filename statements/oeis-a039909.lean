import Mathlib

/-!
# A039909: the largest coefficient of Product_{i=1..n} (1 - q + q^2 - … + (-q)^i) is ~ 6 n^n / e^n

Source: https://oeis.org/A039909
Credit: @Solfanbtc

A039909 (offset 0): `a(n)` is the largest coefficient in the expansion of
`Product_{i=1..n} (1 - q + q^2 - … + (-q)^i)`. Data 1, 1, 2, 5, 20, 101, 573, 3836, …

Conjecture (V. Kotesovec, Jan 05 2023): `a(n) ~ 6 * n^n / exp(n)`.

Definitions. The product is a polynomial in `ℤ[q]` of degree `n(n+1)/2`; `a(n)` is the maximum of
its coefficients of degree `0, …, n(n+1)/2`. Checked with python3: this reproduces the listed
terms, and `a(n) / (6 n^n e^{-n})` is 0.973, 0.986, 0.991, 0.993 at `n = 50, 100, 150, 200`.
-/

namespace OMA.S_oeis_a039909

open Polynomial

/-- `Product_{i=1..n} Sum_{j=0..i} (-q)^j`. -/
noncomputable def P (n : ℕ) : ℤ[X] :=
  ∏ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.range (i + 1), (-X) ^ j

/-- A039909: the largest coefficient of `P n`. -/
noncomputable def a (n : ℕ) : ℤ :=
  (Finset.range (n * (n + 1) / 2 + 1)).sup' ⟨0, by simp⟩ fun k => (P n).coeff k

open Filter Topology in
/-- Kotesovec's conjecture: `a(n) ~ 6 n^n / e^n`. -/
theorem main : Tendsto (fun n : ℕ => (a n : ℝ) / (6 * (n : ℝ) ^ n / Real.exp n)) atTop (𝓝 1) := by
  sorry

end OMA.S_oeis_a039909
