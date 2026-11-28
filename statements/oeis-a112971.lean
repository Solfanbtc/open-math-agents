import Mathlib

/-!
# A112971: Row sums of the matrix ((1,xc(x))^2 mod 2), where c(x) is the g.f. of A000108.

Source: https://oeis.org/A112971
Credit: @Solfanbtc

Conjectures (Paul Barry, OEIS A112971, %C line):
`a(2^n) = a(2^(n+1)+1) = A005578(n)` and `a(2^n-1) = a(3*2^n-1) = 1`.

Definitions.
* `(1, x c(x))` is the Riordan array `T(n, k) = [x^n] (x c(x))^k`, where
  `c(x) = Sum_n Catalan(n) x^n` (A000108). It is lower triangular (`T(n, k) = 0` for `k > n`).
* `a(n) = Sum_{k=0..n} (T^2(n, k) mod 2)`, with `T^2(n, k) = Sum_{i} T(n, i) T(i, k)` the
  matrix square (the sum over `i` may be cut at `n`, as `T` is lower triangular).
* `A005578(n) = ceiling(2^n / 3) = floor(2^n / 3) + 1` (both formulas are in A005578).
* All four equalities are stated for every `n ≥ 0` (`2^0 - 1 = 0`, `3 * 2^0 - 1 = 2`), as the
  data supports (`a(0) = a(1) = a(2) = a(3) = 1`).

Checked with python3: these definitions reproduce all listed %S/%T/%U terms (`n ≤ 99`), and
the conjectures hold for `n ≤ 8` (indices below 520).
-/

namespace OMA.S_oeis_a112971

open PowerSeries

/-- `c(x)`, the generating function of the Catalan numbers A000108. -/
noncomputable def catalanGF : PowerSeries ℕ := PowerSeries.mk fun n => catalan n

/-- The Riordan array `(1, x c(x))`: `T(n, k) = [x^n] (x c(x))^k`. -/
noncomputable def T (n k : ℕ) : ℕ := PowerSeries.coeff n ((X * catalanGF) ^ k)

/-- The matrix square of `T`. -/
noncomputable def T2 (n k : ℕ) : ℕ := ∑ i ∈ Finset.range (n + 1), T n i * T i k

/-- A112971: row sums of `T^2 mod 2`. -/
noncomputable def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), T2 n k % 2

/-- Barry's conjectures for A112971. -/
theorem main : ∀ n : ℕ,
    a (2 ^ n) = 2 ^ n / 3 + 1 ∧ a (2 ^ (n + 1) + 1) = 2 ^ n / 3 + 1 ∧
    a (2 ^ n - 1) = 1 ∧ a (3 * 2 ^ n - 1) = 1 := by
  sorry

end OMA.S_oeis_a112971
