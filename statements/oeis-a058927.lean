import Mathlib

/-!
# A058927: Numerators of series related to triangular cacti.

Source: https://oeis.org/A058927
Credit: @Solfanbtc

The series is `S(x) = x + (1/2) x^3 + (5/8) x^5 + (49/48) x^7 + (243/128) x^9 + ...`
(Bergeron, Labelle, Leroux, *Combinatorial Species and Tree-Like Structures*, p. 307), the
exponential generating function `∑ A034940(n) x^(2n+1)/(2n+1)!` of rooted labeled triangular
cacti with `2n+1` nodes; A034940 gives its defining equation `B(x) = x exp(B(x)^2 / 2)`.
A058927 lists the numerators of its coefficients.

Conjecture (L. Edson Jeffery, Jan 09 2012, in the entry):
`S(x) = ∑_{n ≥ 0} ((2n+1)^(n-1) / (n! 2^n)) x^(2n+1)`.
(Its second half, `a(n) = A052750(n)/d_n` with `d_n = gcd(n!, (2n+1)^(n-1))`, just says that
`a(n)` is the reduced numerator of this coefficient.)
Status: the entry says the conjecture is correct (Andrew Howroyd, Aug 30 2018): it follows from
the formula `A034940(n) = (2n+1)^n (2n)!/(2^n n!)` given in A034940 (Lagrange inversion; Peter
Bala, Jul 31 2012). It is stated here faithfully all the same.

Formal statement, in `ℚ⟦X⟧`: the equation `S = X · exp(S^2 / 2)` (`PowerSeries.subst` of
`(1/2) S^2` into `PowerSeries.exp ℚ`) has a solution, and every solution has
`coeff (2n+1) S = (2n+1)^(n-1) / (n! 2^n)` (an integer power, so `n = 0` gives `1`) and
`coeff (2n) S = 0`, for all `n ≥ 0`.

A python3 check (fixed-point iteration with exact rationals, 30 coefficients): the solution
of `S = x exp(S^2/2)` has exactly these coefficients, and their numerators are the data
`1, 1, 5, 49, 243, 14641, ...`.
-/

namespace OMA.S_oeis_a058927

open PowerSeries

/-- `S` satisfies the defining equation `S = X · exp(S^2 / 2)` of the triangular cacti e.g.f. -/
def IsCactiSeries (S : ℚ⟦X⟧) : Prop :=
  S = X * (PowerSeries.exp ℚ).subst (PowerSeries.C (1 / 2 : ℚ) * S ^ 2)

/-- Jeffery's conjecture (proved, see the docstring):
`S(x) = ∑_{n ≥ 0} ((2n+1)^(n-1) / (n! 2^n)) x^(2n+1)`. -/
theorem main : (∃ S : ℚ⟦X⟧, IsCactiSeries S) ∧
    ∀ S : ℚ⟦X⟧, IsCactiSeries S → ∀ n : ℕ,
      coeff (2 * n + 1) S = ((2 * n + 1 : ℚ) ^ ((n : ℤ) - 1)) / ((n.factorial : ℚ) * 2 ^ n) ∧
      coeff (2 * n) S = 0 := by
  sorry

end OMA.S_oeis_a058927
