import Mathlib

/-!
# A093328: a(n) = 2*n^2 + 3.

Source: https://oeis.org/A093328
Credit: @Solfanbtc

Conjecture (Zak Seidov, OEIS A093328, comment, Sep 27 2015): no term is a perfect power.

Conventions:
* Offset 0: the terms are 2n^2 + 3 for all n ≥ 0 (3, 5, 11, 21, ...).
* A perfect power is `m ^ k` with `m : ℕ` and `k ≥ 2`; the values `m = 0, 1` give 0 and 1,
  which are never terms, so no lower bound on `m` is needed.
* Squares are excluded by a congruence mod 8 (an odd square is 1 mod 8, while 2n^2 + 3 is 3 or 5
  mod 8), so the content is about exponents k ≥ 3. Checked in Python: no term with n ≤ 10^6 is a
  perfect power.
-/

namespace OMA.S_oeis_a093328

/-- Seidov's conjecture: `2 n^2 + 3` is never a perfect power. -/
theorem main : ∀ n m k : ℕ, 2 ≤ k → 2 * n ^ 2 + 3 ≠ m ^ k := by
  sorry

end OMA.S_oeis_a093328
