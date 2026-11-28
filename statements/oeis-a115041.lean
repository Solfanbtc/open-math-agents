import Mathlib

/-!
# A115041: a(n) = y where A115038(x)^2 + prime(n) = y^A115039(n).

Source: https://oeis.org/A115041
Credit: @Solfanbtc

Conjecture (Cino Hilliard, OEIS A115041, also in A115038 and A115039): for every prime `p`
there are `x, y, n` such that `x^2 + p = y^n`, where `y^n` is a perfect power (A115038: the
smallest `x` such that `x^2 + prime(n)` is a perfect power; A115039: the greatest exponent).

Formalization.
* "Perfect power" means exponent `n ≥ 2`; with `n = 1` the claim would be empty (`y = x^2 + p`).
  `x`, `y`, `n` are natural numbers (`x ≥ 0`; `x = 0` never works, since a prime is not a
  perfect power).

Status: this is an easy fact. For an odd prime `p`, `((p - 1)/2)^2 + p = ((p + 1)/2)^2`
(e.g. `498^2 + 997 = 499^2`, the last entry of the table), and for `p = 2`,
`5^2 + 2 = 3^3` (the first entry). It is stated faithfully as posed.

Checked with python3: the smallest such `x` with the greatest exponent reproduces the first
terms of A115038, A115039 and A115041 (`p = 2`: `x = 5`, `27 = 3^3`; `p = 3`: `x = 1`, `4 = 2^2`).
-/

namespace OMA.S_oeis_a115041

/-- For every prime `p`, `x^2 + p` is a perfect power `y^n` (`n ≥ 2`) for some `x`. -/
theorem main : ∀ p : ℕ, p.Prime → ∃ x y n : ℕ, 2 ≤ n ∧ x ^ 2 + p = y ^ n := by
  sorry

end OMA.S_oeis_a115041
