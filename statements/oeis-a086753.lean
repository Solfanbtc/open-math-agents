import Mathlib

/-!
# A086753: Number of distinct entries in a slice of A046816.

Source: https://oeis.org/A086753
Credit: @Solfanbtc

The `n`-th slice of Pascal's tetrahedron A046816 consists of the trinomial coefficients
`n! / (i! j! k!)` with `i + j + k = n`, the coefficients of `(x + y + z)^n`. `a(n)` (offset `0`)
is the number of distinct values among them. This reproduces every term of %S, %T, %U (Python).

Conjecture (Vladimir Reshetnikov, Dec 28 2021): `a(n) ~ (n^2 + 6n - 12)/12`, as asymptotic
equivalence (`Asymptotics.IsEquivalent`: the ratio tends to `1`). Numerically the ratio is
`1.00076` at `n = 100` and `0.99990` at `n = 400`.
-/

namespace OMA.S_oeis_a086753

/-- A086753: the number of distinct trinomial coefficients `n!/(i! j! (n-i-j)!)`. -/
def a (n : ℕ) : ℕ :=
  (((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).filter (fun p => p.1 + p.2 ≤ n)
    |>.image (fun p => n.factorial / (p.1.factorial * p.2.factorial * (n - p.1 - p.2).factorial))).card

theorem main : Asymptotics.IsEquivalent Filter.atTop (fun n : ℕ => (a n : ℝ))
    (fun n : ℕ => ((n : ℝ) ^ 2 + 6 * n - 12) / 12) := by
  sorry

end OMA.S_oeis_a086753
