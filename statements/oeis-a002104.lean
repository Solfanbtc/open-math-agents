import Mathlib

/-!
# A002104: Logarithmic numbers.

Source: https://oeis.org/A002104
Credit: @Solfanbtc

Conjecture (listed in the entry): a(n) + (-n-1)*a(n-1) + 2*(n-1)*a(n-2) + (-n+2)*a(n-3) = 0.

The sequence is taken with the e.g.f. `A(x) = -exp(x) * log(1 - x)` given in the entry
(E. Munarini, Dec 16 2017), i.e. `a n = ∑_{k=1}^{n} C(n,k) * (k-1)!`, so
a(0), a(1), ... = 0, 1, 3, 8, 24, 89, 415, 2372, ...
The recurrence is stated for every `n ≥ 3`, the first `n` for which all its terms are defined
(it was checked numerically for 3 ≤ n < 30); with `a 0 = 0` this also covers the range `n ≥ 4`
should the entry's offset be 1. The integer recurrence is stated in `ℤ`.

The entry also lists a conjectured continued fraction for the ordinary g.f.; that separate
conjecture is not stated here.
-/

namespace OMA.S_oeis_a002104

/-- A002104, the logarithmic numbers: `a n = ∑_{k=1}^{n} C(n,k) (k-1)!`, the coefficients
`n! [x^n]` of `-exp(x) log(1-x)`. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.Icc 1 n, (n.choose k * (k - 1).factorial : ℕ)

/-- The conjectured recurrence
`a(n) + (-n-1) a(n-1) + 2 (n-1) a(n-2) + (-n+2) a(n-3) = 0`, for all `n ≥ 3`. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    a n + (-(n : ℤ) - 1) * a (n - 1) + 2 * ((n : ℤ) - 1) * a (n - 2) +
      (-(n : ℤ) + 2) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a002104
