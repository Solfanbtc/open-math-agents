import Mathlib

/-!
# A060693: Triangle (0 <= k <= n) read by rows: T(n, k) is the number of Schröder paths from (0,0) to (2n,0) having k peaks.

Source: https://oeis.org/A060693
Credit: @Solfanbtc

Conjecture (Werner Schulte, Jan 11 2017, in the %F lines): for every `n ≥ 0`,

  Sum_{k=0..n} (-1)^k * T(n,k) * (n+1-k)^2 = 1 + n + n^2.

Formalization: `T(n, k)` is given by the closed form stated in the entry,
`T(n,k) = binomial(2n-k, k) * A000108(n-k)` (Philippe Deléham, Dec 30 2003), with Mathlib's
`catalan` for the Catalan numbers A000108. It reproduces the listed rows
(1; 1,1; 2,3,1; 5,10,6,1; 14,35,30,10,1; …). Only `0 ≤ k ≤ n` is used, so the natural-number
subtractions `2n - k` and `n - k` are exact, as is `n + 1 - k ≥ 1`; the sum is computed in `ℤ`.
The identity was checked numerically for `n < 60`.
-/

namespace OMA.S_oeis_a060693

/-- A060693: `T(n, k) = binomial(2n-k, k) * Catalan(n-k)` for `0 ≤ k ≤ n`. -/
def T (n k : ℕ) : ℕ := Nat.choose (2 * n - k) k * catalan (n - k)

/-- Schulte's conjecture: `Sum_{k=0..n} (-1)^k T(n,k) (n+1-k)^2 = 1 + n + n^2`. -/
theorem main : ∀ n : ℕ,
    ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * (T n k : ℤ) * ((n + 1 - k : ℕ) : ℤ) ^ 2 =
      1 + (n : ℤ) + (n : ℤ) ^ 2 := by
  sorry

end OMA.S_oeis_a060693
