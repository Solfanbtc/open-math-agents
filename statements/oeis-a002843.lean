import Mathlib

/-!
# A002843: Number of partitions of n into parts 1/2, 3/4, 7/8, 15/16, etc.

Source: https://oeis.org/A002843
Credit: @Solfanbtc

Conjecture (Bill McEachen, Feb 05 2026, in the entry): `a(n) ~ A102375 * a(n-1)`, i.e.
`a(n+1) / a(n) → A102375 = 1.79414718754168546...`.

Conventions:
* `a(n)` is the number of multisets of parts `1 - 2^(-k)` (`k ≥ 1`) with sum `n`, encoded as
  multisets of exponents `k ≥ 1`. `a(0) = 1` (the empty partition). Checked in python against the
  data `1, 1, 2, 4, 7, 13, 24, 43` for `n ≤ 7` (it also agrees with the comment's description as
  compositions with `a_i ≤ 2 a_(i-1)`, and with the g.f. `1/(1 - F)` below, for `n < 20`).
* A102375 is the reciprocal of the smallest positive `x` with `F(x) = 1`, where
  `F(x) = ∑_{j ≥ 1} (-1)^(j+1) x^(2^(j+1)-2-j) / ((1-x)(1-x^3)(1-x^7)⋯(1-x^(2^j-1)))`.
  The name of A102375 says "smallest positive zero of `F`", but its Mathematica program and its
  digits use `F(x) = 1` (root `x ≈ 0.5573678720`, reciprocal `1.7941471875416…`, matching the
  data), whereas the smallest positive zero of `F` itself is near `0.948`. We follow the program
  and the data. Below, `F` is reindexed with `j ↦ j + 1`.
* `a(n) ~ c * a(n-1)` is read as `a(n+1) / a(n) → c`. The constant is given by its defining
  property: there is a smallest positive root `x₀` of `F x = 1`, and the ratio tends to `1 / x₀`.
-/

namespace OMA.S_oeis_a002843

open Filter Topology

/-- `a(n)`: number of partitions of `n` into parts `1 - 2^(-k)`, `k ≥ 1`
(a partition is a multiset of exponents `k`). -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {s : Multiset ℕ | (∀ k ∈ s, 1 ≤ k) ∧
    (s.map fun k : ℕ => (1 : ℚ) - 1 / 2 ^ k).sum = n}

/-- `F(x) = ∑_{j ≥ 0} (-1)^j x^(2^(j+2)-3-j) / ∏_{k=1}^{j+1} (1 - x^(2^k-1))`. -/
noncomputable def F (x : ℝ) : ℝ :=
  ∑' j : ℕ, (-1 : ℝ) ^ j * x ^ (2 ^ (j + 2) - 3 - j) /
    ∏ k ∈ Finset.Icc 1 (j + 1), (1 - x ^ (2 ^ k - 1))

/-- `a(n+1) / a(n)` tends to A102375 `= 1 / x₀`, where `x₀` is the smallest positive root of
`F x = 1`. -/
theorem main : ∃ x₀ : ℝ, 0 < x₀ ∧ F x₀ = 1 ∧ (∀ y : ℝ, 0 < y → y < x₀ → F y ≠ 1) ∧
    Tendsto (fun n : ℕ => (a (n + 1) : ℝ) / a n) atTop (𝓝 (1 / x₀)) := by
  sorry

end OMA.S_oeis_a002843
