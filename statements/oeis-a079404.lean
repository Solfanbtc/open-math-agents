import Mathlib

/-!
# A079404: Let G(n) be the set of numbers between 2^(n-1) and 2^n-1, inclusive. There is a unique number m(n) in G(n) so that the denominator of the m(n)-th partial sum of the double harmonic series is divisible by smaller 2-power than that of others in G(n). This power is defined to be a(n).

Source: https://oeis.org/A079404
Credit: @Solfanbtc

The `m`-th partial sum of the double harmonic series is `S(m) = ∑_{1 ≤ k < l ≤ m} 1/(k l)`
(as in the example: `S(4) = 35/24`, `S(6) = 203/90`). For `n ≥ 2` (offset 2), `a(n)` is the
least 2-adic valuation of the (reduced) denominator of `S(m)` over
`m ∈ G(n) = [2^(n-1), 2^n - 1]`. Defining `a(n)` as this minimum does not depend on the
uniqueness claim in the name. Checked with python3 for `2 ≤ n ≤ 13`: this gives the data
0, 1, 1, 3, 4, 3, 3, 5, 7, 9, 10, 9, and the minimum is attained at a single `m` each time.

Conjecture (J. Zhao, Partial sums of multiple zeta value series II, arXiv:math/0303043, (24)):
`a(n) → ∞`. `main` states this.
-/

namespace OMA.S_oeis_a079404

open Filter

/-- `S m = ∑_{1 ≤ k < l ≤ m} 1/(k l)`. -/
def S (m : ℕ) : ℚ := ∑ l ∈ Finset.Icc 1 m, ∑ k ∈ Finset.Ico 1 l, (1 : ℚ) / (k * l)

/-- `a n`: the least 2-adic valuation of the denominator of `S m` for `2^(n-1) ≤ m ≤ 2^n - 1`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {v : ℕ | ∃ m ∈ Finset.Icc (2 ^ (n - 1)) (2 ^ n - 1), v = padicValNat 2 (S m).den}

theorem main : Tendsto a atTop atTop := by
  sorry

end OMA.S_oeis_a079404
