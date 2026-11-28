import Mathlib

/-!
# A101229: Perfect inverse 3x+1 conjecture (See comments for rules).

Source: https://oeis.org/A101229
Credit: @Solfanbtc

Rules (A. Wajnberg, OEIS %C), starting from `a(1) = 1`. Rule 2: if the current term `n'` is of
the form `3x + 1`, with `x = (n' - 1)/3` a positive integer, the next term is `x`. Rule 1:
otherwise the next term is `2 n'`. Additional rule: rule 2 is applied at most once for any
given number `n'`; when the same value comes back, rule 1 is used. This gives
`1, 2, 4, 1, 2, 4, 8, 16, 5, 10, 3, 6, 12, ...`: the first `4` goes to `1` by rule 2, and the
second `4` goes to `8` by rule 1. Reading rule 2 as needing a positive `x` is what makes
`1 ↦ 2` (since `1 = 3·0 + 1`), as in the data.

Claim (OEIS %C, with the explicit formula of J. Krizek, Aug 17 2009, in %F): the sequence
falls into `3, 6, 12, 24, ...` and never again meets a number to which rule 2 applies, that is
`a(n) = 3 · 2^(n-11)` for `n ≥ 11`. This is elementary (multiples of 3 are never `3x + 1`);
the entry calls it a conjecture only in its name. Here `a n` is 1-indexed as in the OEIS,
`a 0` is the junk value `1`.
-/

namespace OMA.S_oeis_a101229

/-- One step: `(current term, values to which rule 2 was already applied)`. -/
def step (s : ℕ × List ℕ) : ℕ × List ℕ :=
  if s.1 % 3 = 1 ∧ 1 ≤ (s.1 - 1) / 3 ∧ s.1 ∉ s.2 then ((s.1 - 1) / 3, s.1 :: s.2)
  else (2 * s.1, s.2)

/-- `a n` is A101229(n) for `n ≥ 1`. -/
def a (n : ℕ) : ℕ := (step^[n - 1] (1, [])).1

theorem main : ∀ n : ℕ, 11 ≤ n → a n = 3 * 2 ^ (n - 11) := by
  sorry

end OMA.S_oeis_a101229
