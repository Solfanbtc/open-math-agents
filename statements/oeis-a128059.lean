import Mathlib

/-!
# A128059: a(n) = numerator((2*n-1)^2/(2*(2*n)!)).

Source: https://oeis.org/A128059
Credit: @Solfanbtc

Conjecture (Yalcin Aktar, Jul 23 2008): a(n) = denominator(f(n-1)) with
f(n) = lcm(2,3,4,5,...,n) * (Sum_{k=0..n} frac(Bernoulli(2*k)) * binomial(n+k,k)).

Formalization.
* a(n) (offset 0) is the numerator of the rational (2n-1)^2 / (2 (2n)!) (with 2n - 1 computed
  in ℤ, so a(0) = numerator(1/2) = 1); data 1, 1, 3, 5, 7, 1, 11, ...
* frac is the fractional part x - floor(x) (`Int.fract`), Bernoulli numbers are Mathlib's
  `bernoulli` (only even indices occur, so the sign convention for B_1 is irrelevant), and
  lcm(2, ..., m) is the lcm of the integers from 2 to m (1 when m < 2).
* Statement: for every n ≥ 1 (so that f(n-1) is defined), a(n) = denominator(f(n-1)).
python3 (exact rationals): holds for 1 ≤ n < 70.
-/

namespace OMA.S_oeis_a128059

/-- A128059(n). -/
def a (n : ℕ) : ℕ := (((2 * (n : ℤ) - 1) ^ 2 : ℚ) / (2 * (2 * n).factorial)).num.natAbs

/-- Aktar's f(m). -/
noncomputable def f (m : ℕ) : ℚ :=
  ((Finset.Icc 2 m).lcm id : ℕ) *
    ∑ k ∈ Finset.range (m + 1), Int.fract (bernoulli (2 * k)) * ((m + k).choose k : ℚ)

theorem main : ∀ n : ℕ, 1 ≤ n → (f (n - 1)).den = a n := by
  sorry

end OMA.S_oeis_a128059
