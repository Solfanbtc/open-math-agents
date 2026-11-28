import Mathlib

/-!
# A080894: Expansion of the exponential series exp(x M(x)), M the Motzkin g.f.

Source: https://oeis.org/A080894
Credit: @Solfanbtc

A080894 has e.g.f. `exp(x M(x)) = exp((1 - x - sqrt(1 - 2x - 3x^2))/(2x))`, where
`M(x) = Σ_n Motzkin(n) x^n` is the g.f. of the Motzkin numbers A001006,
`Motzkin(n) = Σ_k binomial(n, 2k) Catalan(k)`. (The entry's name writes
`(1 - sqrt(1-2x-3x^2))/(2x)` in the exponent, which differs from `x M(x)` by the constant `1/2`.
The %F line and the data, `a(0) = a(1) = 1`, use `x M(x)`.) Since `x M(x)` has no constant
term, `exp(x M(x))` agrees modulo `x^(n+1)` with `Σ_{k ≤ n} (x M(x))^k / k!`, so
`a(n) = n! [x^n] Σ_{k ≤ n} (x M(x))^k / k!`.

Conjecture (R. J. Mathar, 2020): `a` is D-finite with the recurrence
`(-2n+3) a(n) + (-2n^3+9n^2-9n+1) a(n-1) + (n-1)(n-2)(4n^2-2n-3) a(n-2)`
`+ 3(n-1)(n-3)(2n-1)(n-2)^2 a(n-3) = 0`, for `n ≥ 3` (the first `n` where all terms are
defined). Checked with python3 (exact rationals): the definition reproduces the 18 listed terms
and the recurrence holds for `3 ≤ n < 60`.
-/

namespace OMA.S_oeis_a080894

open PowerSeries

/-- Motzkin numbers A001006. -/
def motzkin (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n / 2 + 1), n.choose (2 * k) * catalan k

/-- `x M(x)`. -/
noncomputable def xM : PowerSeries ℚ := X * PowerSeries.mk fun n => (motzkin n : ℚ)

/-- A080894(n) = n! [x^n] exp(x M(x)). -/
noncomputable def a (n : ℕ) : ℚ :=
  (n.factorial : ℚ) *
    coeff n (∑ k ∈ Finset.range (n + 1), (1 / (k.factorial : ℚ)) • xM ^ k)

/-- Mathar's conjectured recurrence. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    (-2 * (n : ℚ) + 3) * a n + (-2 * (n : ℚ) ^ 3 + 9 * n ^ 2 - 9 * n + 1) * a (n - 1) +
      ((n : ℚ) - 1) * (n - 2) * (4 * n ^ 2 - 2 * n - 3) * a (n - 2) +
      3 * ((n : ℚ) - 1) * (n - 3) * (2 * n - 1) * (n - 2) ^ 2 * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a080894
