import Mathlib

/-!
# A092959: least square that is a product of n successive terms of an AP, plus 1.

Source: https://oeis.org/A092959
Credit: @Solfanbtc

A092959(n) is the least square of the form `a (a+d) ⋯ (a+(n-1)d) + 1`, a product of `n`
successive terms of an arithmetic progression of positive integers plus one, or `0` if there
is none. The progression has `a ≥ 1` and common difference `d ≥ 1`. A constant progression is
not allowed: with `d = 0`, `2^3 + 1 = 9` would give `a(3) ≤ 9`, but `a(3) = 16 = 1·3·5 + 1`.
A negative `d` only reverses a progression. E.g. `a(4) = 25 = 1·2·3·4 + 1`. Checked with
python3 (`a, d < 120`): the values `4, 4, 16, 25, 121, 5041, 5041` for `n = 1..7` are
reproduced.

Conjecture (entry): no term is zero, i.e. for every `n ≥ 1` some such product plus one is a
perfect square. (The data lists `0` for `n = 8` and `n ≥ 10`. David Wasserman found no square
up to `10^(3n+8)` and remarks that zero values are highly probable but unproved, so the
conjecture may well be false.)
-/

namespace OMA.S_oeis_a092959

/-- The conjecture: for every `n ≥ 1`, some product of `n` successive terms of an arithmetic
progression of positive integers, plus one, is a square. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ a d m : ℕ, 1 ≤ a ∧ 1 ≤ d ∧
    (∏ i ∈ Finset.range n, (a + i * d)) + 1 = m ^ 2 := by
  sorry

end OMA.S_oeis_a092959
