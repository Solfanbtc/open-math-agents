import Mathlib

/-!
# A027261: a(n) = Sum_{k=0..2n} (k+1) * A025177(n, k).

Source: https://oeis.org/A027261
Credit: @Solfanbtc

A025177 is the triangle `T(n, k)`, `0 ≤ k ≤ 2n`, with rows `[1]`, `[1, 0, 1]` and
`T(n, k) = T(n-1, k-2) + T(n-1, k-1) + T(n-1, k)` (zero outside `0 ≤ k ≤ 2n`). Equivalently,
row `n ≥ 1` is the coefficient list of `(1 + X^2) * (1 + X + X^2)^(n-1)`, and row `0` is `1`
(this matches the PARI formula `T(n,k) = [x^k](1+x+x^2)^n - [x^(k-1)](1+x+x^2)^(n-1)`).

Conjecture (Ralf Stephan, 2004): `a(n) = 2(n+1) * 3^(n-1)` for `n > 1`. The other conjectures in
the entry, Colin Barker's `a(n) = 6a(n-1) - 9a(n-2)` for `n > 3` and the g.f.
`(1-2x+3x^2)/(1-3x)^2`, follow from this one together with `a(0) = 1` and `a(1) = 4`.
Checked with python3: these definitions reproduce the data of A025177 (rows 0..5) and all 27
listed terms of A027261, and the closed form holds for `2 ≤ n ≤ 26`.
-/

namespace OMA.S_oeis_a027261

open Polynomial

/-- Row `n` of A025177 as a polynomial: `T(n, k)` is its coefficient of `X^k`. -/
noncomputable def rowPoly : ℕ → ℕ[X]
  | 0 => 1
  | n + 1 => (1 + X ^ 2) * (1 + X + X ^ 2) ^ n

/-- A025177(n, k). -/
noncomputable def T (n k : ℕ) : ℕ := (rowPoly n).coeff k

/-- A027261(n) = Σ_{k=0}^{2n} (k+1) T(n, k). -/
noncomputable def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (2 * n + 1), (k + 1) * T n k

/-- The conjecture: `a(n) = 2(n+1) 3^(n-1)` for `n > 1`. -/
theorem main : ∀ n : ℕ, 1 < n → a n = 2 * (n + 1) * 3 ^ (n - 1) := by
  sorry

end OMA.S_oeis_a027261
