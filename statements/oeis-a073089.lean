import Mathlib

/-!
# A073089: a(n) = (1/2)(4n - 3 - Sum_{k=1..n} A007400(k))

Source: https://oeis.org/A073089
Credit: @Solfanbtc

A007400 (offset 0) is the continued fraction of `κ = ∑_{n ≥ 0} 1/2^(2^n) = 0.8164215…`:
`0; 1, 4, 2, 4, 4, 6, 4, 2, …`. Below, `A007400(k)` for `k ≥ 1` is the `k`-th partial denominator of
Mathlib's (regular) continued fraction `GenContFract.of κ` (its `(k-1)`-th entry of `partDens`;
`κ` is irrational, so the expansion is infinite). A073089 (offset 1):
`a(n) = (4n - 3 - ∑_{k=1}^{n} A007400(k))/2`: `0, 0, 1, 1, 1, 0, 0, 1, …` (an exact computation of
the continued fraction reproduces the A007400 and A073089 data).

A057661: `A057661(m) = ∑_{k=1}^{m} lcm(m, k)/m`.

Conjecture (Velin Yanev, Feb 01 2021, OEIS formula): `a(n) = (1 + (-1)^A057661(n-1))/2` for all
`n > 1`. (The entry also contains a comment sketching a proof of this formula via
`A057661(m) = (1 + ∑_{d ∣ m} d φ(d))/2`.) Python: holds for `2 ≤ n < 200`.
-/

namespace OMA.S_oeis_a073089

/-- `κ = ∑_{n ≥ 0} 1/2^(2^n)`. -/
noncomputable def kappa : ℝ := ∑' n : ℕ, (1 / 2 : ℝ) ^ (2 ^ n)

/-- A007400(k), `k ≥ 1`: the `k`-th partial denominator of the continued fraction of `κ`. -/
noncomputable def A007400 (k : ℕ) : ℝ := ((GenContFract.of kappa).partDens.get? (k - 1)).getD 0

/-- A073089. -/
noncomputable def a (n : ℕ) : ℝ := (4 * n - 3 - ∑ k ∈ Finset.Icc 1 n, A007400 k) / 2

/-- A057661: `∑_{k=1}^{m} lcm(m, k)/m`. -/
def A057661 (m : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 m, Nat.lcm m k / m

/-- Yanev's conjecture: `a(n) = (1 + (-1)^A057661(n-1))/2` for `n > 1`. -/
theorem main : ∀ n : ℕ, 1 < n → a n = (1 + (-1 : ℝ) ^ A057661 (n - 1)) / 2 := by
  sorry

end OMA.S_oeis_a073089
