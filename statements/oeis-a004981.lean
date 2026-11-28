import Mathlib

/-!
# A004981: `a(n) = (2^n/n!) * Product_{k=0..n-1} (4k + 1)`

Source: https://oeis.org/A004981
Credit: @Solfanbtc

`a(n) = 2^n ∏_{k<n} (4k+1) / n!` (offset 0; g.f. `(1-8x)^(-1/4)`): `1, 2, 10, 60, 390, …`.
The quotient is always an integer (it is `(-8)^n binom(-1/4, n)`), so the natural-number
division below is exact; the definition reproduces all 23 data terms.

Conjecture (Peter Bala, Dec 22 2019, OEIS comment): `a(p n) ≡ a(n) (mod p^2)` for every prime
`p ≡ 1 (mod 4)` and every positive integer `n`. (Checked with Python for
`p ∈ {5, 13, 17, 29, 37, 41}`, `1 ≤ n ≤ 11`; it fails for `p = 3, 7, 11`.)
-/

namespace OMA.S_oeis_a004981

/-- A004981: `a(n) = 2^n ∏_{k=0}^{n-1} (4k+1) / n!`. -/
def a (n : ℕ) : ℕ := 2 ^ n * (∏ k ∈ Finset.range n, (4 * k + 1)) / n.factorial

/-- Bala's conjecture: `a(p n) ≡ a(n) (mod p^2)` for primes `p ≡ 1 (mod 4)` and `n ≥ 1`. -/
theorem main : ∀ p : ℕ, p.Prime → p % 4 = 1 → ∀ n : ℕ, 1 ≤ n →
    a (p * n) ≡ a n [MOD p ^ 2] := by
  sorry

end OMA.S_oeis_a004981
