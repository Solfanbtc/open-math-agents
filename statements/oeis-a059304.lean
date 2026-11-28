import Mathlib

/-!
# A059304: 2^n (2n)!/(n!)^2 = Sum_{j,k ≤ n} C(n,j) C(n,k) C(j+k,n)

Source: https://oeis.org/A059304
Credit: @Solfanbtc

A059304 (offset 0): `a(n) = 2^n * (2n)! / (n!)^2 = 2^n binomial(2n, n)`.

The entry: "Theorem: For n >= 0, a(n) = Sum_{0 <= j, k <= n} binomial(n, j)*binomial(n, k)*
binomial(j+k, n). [Conjectured by Peter Bala, Jul 16 2024]", with a proof by K. Kitamura
(Aug 04 2026): the sum is `[x^n] (Sum_j binomial(n, j) (1+x)^j)^2 = [x^n] (2 + x)^(2n)`.
`main` states the identity for every `n ≥ 0`. Checked with python3 for `0 ≤ n < 60`.
-/

namespace OMA.S_oeis_a059304

/-- A059304: `2^n (2n)!/(n!)^2`. -/
def a (n : ℕ) : ℕ := 2 ^ n * (2 * n).factorial / (n.factorial) ^ 2

/-- Bala's identity (proved by Kitamura). -/
theorem main : ∀ n : ℕ, a n = ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
    n.choose j * n.choose k * (j + k).choose n := by
  sorry

end OMA.S_oeis_a059304
