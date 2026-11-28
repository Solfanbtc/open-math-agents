import Mathlib

/-!
# A079489: Bala's supercongruences for the powers of its g.f. and of the associated reversion

Source: https://oeis.org/A079489
Credit: @Solfanbtc

A079489 (offset 0): `a(n) = (2·4^n·binomial(2n, n) - binomial(4n + 1, 2n))/(n + 1)`;
data 1, 3, 22, 211, 2306, 27230, … Let `A(x) = Sum_n a(n) x^n`.

Conjectures (P. Bala, Oct 23 2024): "For integer r and positive integer s, define a sequence
{u(n) : n >= 0} by setting u(n) = [x^(s*n)] A(x)^(r*n). We conjecture that the supercongruence
u(n*p^k) == u(n*p^(k-1)) (mod p^(3*k)) holds for all primes p >= 5 and for all positive integers
n and k. Let B(x) = 1/x * series_reversion(x*A(x)). Define a sequence {v(n) : n >= 0} by setting
v(n) = [x^(s*n)] B(x)^(r*n). We conjecture that the supercongruence v(n*p^k) == v(n*p^(k-1))
(mod p^(3*k)) holds for all primes p >= 5 and for all positive integers n and k."

Lean details. We work in `ℚ⟦X⟧`. `A` has constant term 1, so integer powers `A^m` (`m < 0`
meaning powers of `A⁻¹`) are defined, and they have integer coefficients. `w = x B(x)` is the
compositional inverse of `x A(x)`, i.e. `w A(w) = x`, equivalently `B(x) A(x B(x)) = 1` with
`B(0) = 1`; this equation determines `B` uniquely, so `main` quantifies over every `B` with
`B(0) = 1` and `B * A(X * B) = 1` (`PowerSeries.subst`). A congruence `y ≡ z (mod p^(3k))`
between these rational (in fact integer) values is written `y - z = p^(3k) · m` with `m ∈ ℤ`.
Checked with python3 (exact integers; `B` by fixed-point iteration): both congruences hold for
`r ∈ {-2, -1, 1, 2, 3}`, `s ∈ {1, 2}`, `p ∈ {5, 7}`, `k ∈ {1, 2}`, `n ∈ {1, 2}` whenever
`s n p^k < 130` (150 cases).
-/

namespace OMA.S_oeis_a079489

open PowerSeries

/-- A079489. -/
def a (n : ℕ) : ℚ := (2 * 4 ^ n * ((2 * n).choose n : ℚ) - ((4 * n + 1).choose (2 * n) : ℚ)) / (n + 1)

/-- The g.f. `A(x)`. -/
def A : PowerSeries ℚ := PowerSeries.mk a

/-- Integer powers of a power series (negative exponents use `⁻¹`). -/
noncomputable def zpow' (F : PowerSeries ℚ) (m : ℤ) : PowerSeries ℚ :=
  if 0 ≤ m then F ^ m.toNat else F⁻¹ ^ (-m).toNat

/-- `y ≡ z (mod p^(3k))` for rationals with integer difference quotient. -/
def SuperCong (p k : ℕ) (y z : ℚ) : Prop := ∃ m : ℤ, y - z = (p : ℚ) ^ (3 * k) * m

/-- Bala's two supercongruence conjectures for A079489. -/
theorem main : ∀ (r : ℤ) (s : ℕ), 0 < s → ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ n k : ℕ, 0 < n → 0 < k →
    SuperCong p k (coeff (s * (n * p ^ k)) (zpow' A (r * (n * p ^ k : ℕ))))
      (coeff (s * (n * p ^ (k - 1))) (zpow' A (r * (n * p ^ (k - 1) : ℕ)))) ∧
    ∀ B : PowerSeries ℚ, constantCoeff B = 1 → B * A.subst (X * B) = 1 →
      SuperCong p k (coeff (s * (n * p ^ k)) (zpow' B (r * (n * p ^ k : ℕ))))
        (coeff (s * (n * p ^ (k - 1))) (zpow' B (r * (n * p ^ (k - 1) : ℕ)))) := by
  sorry

end OMA.S_oeis_a079489
