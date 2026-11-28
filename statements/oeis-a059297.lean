import Mathlib

/-!
# A059297: Triangle of idempotent numbers `binomial(n,k) * k^(n-k)`, version 1

Source: https://oeis.org/A059297
Credit: @Solfanbtc

`T(n, k) = C(n, k) k^(n-k)` for `0 ≤ k ≤ n` (offset 0, `0^0 = 1`): `1; 0, 1; 0, 2, 1; 0, 3, 6, 1; …`.
A137452: the coefficients of the Abel polynomials `A(n, x) = x (x - n)^(n-1)`, i.e.
`S(n, k) = [x^k] x (x - n)^(n-1)` for `n ≥ 1`, and `A(0, x) = 1` (the data begin `1; 0, 1;
0, -2, 1; 0, 9, -6, 1; …`). Both triangles are lower triangular (entries with `k > n` are `0`)
and reproduce their data.

Conjecture (R. J. Mathar, Mar 12 2013, OEIS comment): the matrix inverse of this triangle is
A137452. Status: PROVED (Peter Bala, Apr 08 2013, OEIS comment: this triangle is the
exponential Riordan array `[1, x e^x]`, so its inverse is `[1, W(x)]` with `W` the Lambert
function, which is A137452). Stated faithfully: as infinite lower-triangular matrices
`T S = S T = I`, i.e. for all `n, k`, `∑_{m=0}^{n} T(n, m) S(m, k) = [n = k]` and
`∑_{m=0}^{n} S(n, m) T(m, k) = [n = k]` (only `m ≤ n` contribute). Python: checked for
`n, k < 25`.
-/

namespace OMA.S_oeis_a059297

open Polynomial

/-- A059297: `T(n, k) = C(n, k) k^(n-k)` (zero for `k > n`). -/
def T (n k : ℕ) : ℤ := (Nat.choose n k : ℤ) * (k : ℤ) ^ (n - k)

/-- The Abel polynomial `A(n, x) = x (x - n)^(n-1)`, with `A(0, x) = 1`. -/
noncomputable def abel (n : ℕ) : ℤ[X] := if n = 0 then 1 else X * (X - C (n : ℤ)) ^ (n - 1)

/-- A137452: `S(n, k)` is the coefficient of `x^k` in the Abel polynomial `A(n, x)`. -/
noncomputable def S (n k : ℕ) : ℤ := (abel n).coeff k

/-- The inverse of the triangle A059297 is A137452 (proved by Bala). -/
theorem main : ∀ n k : ℕ,
    (∑ m ∈ Finset.range (n + 1), T n m * S m k) = (if n = k then 1 else 0) ∧
    (∑ m ∈ Finset.range (n + 1), S n m * T m k) = (if n = k then 1 else 0) := by
  sorry

end OMA.S_oeis_a059297
