import Mathlib

/-!
# A077361: Smallest n-digit prime whose external and internal digits form primes

Source: https://oeis.org/A077361
Credit: @Solfanbtc

A `d`-digit prime `p` (`d ≥ 3`) qualifies if its external digits (first and last digit, read as the
two-digit number `first·10 + last`) form a prime, and its internal digits (the middle `d - 2`
digits, read as a number, leading zeros dropped) form a prime; e.g. `1021`: `11` and `02 = 2`;
`10037`: `17` and `003 = 3`. A077361 lists the smallest such prime with `n` digits, or `0` if there
is none: `0, 0, 127, 1021, 10037, …` (a search reproduces `127, 1021, …, 10000000033` for
`d = 3..11`). The listed offset is 0, but the data are indexed so that the third term `127` is the
3-digit one; the name's `n` is the number of digits.

Conjecture (OEIS comment): no entry is zero for `n > 2`. Stated with `n` the number of digits (as
in the name): for every `d ≥ 3` there is a `d`-digit prime of this kind. (Under the literal offset
the claim would only concern `d ≥ 4`, a consequence of this statement.)
-/

namespace OMA.S_oeis_a077361

/-- `p` is a `d`-digit prime whose external and internal digits form primes. -/
def Good (d p : ℕ) : Prop :=
  10 ^ (d - 1) ≤ p ∧ p < 10 ^ d ∧ p.Prime ∧
    (p / 10 ^ (d - 1) * 10 + p % 10).Prime ∧ (p / 10 % 10 ^ (d - 2)).Prime

/-- For every `d ≥ 3` some `d`-digit prime has prime external and internal digits. -/
theorem main : ∀ d : ℕ, 3 ≤ d → ∃ p : ℕ, Good d p := by
  sorry

end OMA.S_oeis_a077361
