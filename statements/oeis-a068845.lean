import Mathlib

/-!
# A068845: Final digits of the smallest prime starting with n!.

Source: https://oeis.org/A068845
Credit: @Solfanbtc

Conjecture (OEIS A068845, comment): the terms are noncomposite numbers, i.e. each a(n) is 1 or
a prime.

Conventions:
* A prime "starting with n!" is p = n! · 10^d + r with d ≥ 1 appended digits and 0 ≤ r < 10^d
  (d = 0 is excluded: a(2) = 3 comes from 23, not from 2! = 2 itself). The smallest such prime is
  `P n` (`sInf`); d and r are determined by p. a(n) is r, the number formed by the final digits,
  leading zeros dropped. The data has a(7) = 1 from 504001 = 7!·100 + 1 (prime), whereas the
  example's "504011" seems to be a slip (504001 < 504011 is prime).
* Offset 1; the conjecture is stated for every n ≥ 1: if P n = n! · 10^d + r with d ≥ 1 and
  r < 10^d, then r = 1 or r is prime.
* Checked in Python (Miller-Rabin): this reproduces all 26 terms of %S, and the conjecture holds
  for 1 ≤ n < 150.
-/

namespace OMA.S_oeis_a068845

/-- The smallest prime whose decimal expansion starts with that of `n!` (with ≥ 1 more digit). -/
noncomputable def P (n : ℕ) : ℕ :=
  sInf {p : ℕ | p.Prime ∧ ∃ d, 1 ≤ d ∧ ∃ r < 10 ^ d, p = n.factorial * 10 ^ d + r}

/-- The final digits of `P n` are `1` or a prime. -/
theorem main :
    ∀ n d r : ℕ, 1 ≤ n → 1 ≤ d → r < 10 ^ d → P n = n.factorial * 10 ^ d + r →
      r = 1 ∨ r.Prime := by
  sorry

end OMA.S_oeis_a068845
