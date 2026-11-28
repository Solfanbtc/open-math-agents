import Mathlib

/-!
# A020735: Odd numbers >= 5.

Source: https://oeis.org/A020735
Credit: @Solfanbtc

The entry (comment by Charles R Greathouse IV, Jun 20 2019) says: Sun conjectures that any member
of this sequence (an odd number `n ≥ 5`) is of the form `m^2 + m + p`, where `p` is prime.

The conjecture is Z.-W. Sun, *On sums of primes and triangular numbers*, arXiv:0803.3737,
Conjecture 1.4, where `m` (written `x` there) is a *positive* integer; see also OEIS A228446
("2*n+1 = p + x*(x+1) for some positive integer x"). We therefore require `0 < m`, as in the
source. (With `m = 0` allowed the claim would be weaker.) The bound `5 ≤ n` is needed: `3` is not
of this form. Checked numerically for all odd `5 ≤ n ≤ 200000`.
-/

namespace OMA.S_oeis_a020735

/-- Sun's conjecture: every odd `n ≥ 5` is `m^2 + m + p` with `m` a positive integer and `p` prime. -/
theorem main : ∀ n : ℕ, Odd n → 5 ≤ n → ∃ m p : ℕ, 0 < m ∧ p.Prime ∧ n = m ^ 2 + m + p := by
  sorry

end OMA.S_oeis_a020735
