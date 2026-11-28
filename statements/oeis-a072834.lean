import Mathlib

/-!
# A072834: Exponents occurring in expansion of F_8(q^2).

Source: https://oeis.org/A072834
Credit: @Solfanbtc

The entry lists, in increasing order (offset 0), the exponents with a nonzero coefficient in
the series given by the Mathematica program of the entry (G. C. Greubel), with Ramanujan's
`f(x, y) = ∑_{n ∈ ℤ} x^(n(n+1)/2) y^(n(n-1)/2)`:

  `(f(q^4,q^4)^7 + (2 q f(q^8,q^24))^7 + 14 f(q^2,q^2)^2 f(q^4,q^4)^5
      - 7 f(q^4,q^4)^3 f(q^2,q^2)^4) / 8`

(see S. Ahlgren, The sixth, eighth, ninth and tenth powers of Ramanujan's theta function,
Proc. AMS 128 (2000)). Here `f(q^s,q^s) = ∑_{n ∈ ℤ} q^(s n^2)` and
`q f(q^8,q^24) = ∑_{n ∈ ℤ} q^(16 n^2 - 8 n + 1) = ∑_{n ∈ ℤ} q^((4n-1)^2)`.
We checked that the nonzero exponents of this series below 600 are exactly the listed terms
0, 7, 12, 15, 16, 23, ..., 247 of %S, %T, %U.

Conjecture (Jerzy R. Borysowicz, 2022): `a(n) = 4 n + pa(n mod 4)` with
`pa(0..3) = 0, 3, 4, 3`. The other parts of the conjecture (`a(n)/n → 4`, `a(n)/n ≥ 4`,
`a(n+4) = a(n) + 16`) follow directly from this formula, so `main` states the formula,
with `a` the increasing enumeration (`Nat.nth`) of the exponents with nonzero coefficient.
-/

namespace OMA.S_oeis_a072834

/-- `f(q^s, q^s) = ∑_{n ∈ ℤ} q^(s n^2)`: the coefficient of `q^m` counts the integers `n`
with `s n^2 = m` (all such `n` satisfy `|n| ≤ m`). -/
noncomputable def theta (s : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun m =>
    (((Finset.Icc (-(m : ℤ)) m).filter fun n => (s : ℤ) * n ^ 2 = m).card : ℚ)

/-- `2 q f(q^8, q^24) = 2 ∑_{n ∈ ℤ} q^((4n-1)^2)` (all such `n` satisfy `|n| ≤ m`). -/
noncomputable def psiTerm : PowerSeries ℚ :=
  PowerSeries.mk fun m =>
    2 * (((Finset.Icc (-(m : ℤ)) m).filter fun n => (4 * n - 1) ^ 2 = (m : ℤ)).card : ℚ)

/-- The series whose nonzero exponents form A072834. -/
noncomputable def F8 : PowerSeries ℚ :=
  (1 / 8 : ℚ) • (theta 4 ^ 7 + psiTerm ^ 7 + 14 * theta 2 ^ 2 * theta 4 ^ 5
    - 7 * theta 4 ^ 3 * theta 2 ^ 4)

/-- `a(n)`, offset 0: the `n`-th exponent (in increasing order) with a nonzero coefficient. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.nth (fun m => PowerSeries.coeff m F8 ≠ 0) n

/-- `pa(k) = 0, 3, 4, 3` for `k = 0, 1, 2, 3`. -/
def pa : ℕ → ℕ
  | 0 => 0
  | 1 => 3
  | 2 => 4
  | _ => 3

/-- Borysowicz's conjecture: `a(n) = 4 n + pa(n mod 4)` for all `n ≥ 0`. -/
theorem main : ∀ n : ℕ, a n = 4 * n + pa (n % 4) := by
  sorry

end OMA.S_oeis_a072834
