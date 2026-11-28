import Mathlib

/-!
# A000918: a(n) = 2^n - 2, and the integers below 10^n using only the digits 8 and 9

Source: https://oeis.org/A000918
Credit: @Solfanbtc

The entry (offset 0) says: "For n >= 1, conjectured to be the number of integers from 0 to
(10^n)-1 that lack 0, 1, 2, 3, 4, 5, 6 and 7 as a digit." (A. Wajnberg, Apr 25 2005)

Index fix. Read literally, the claim fails at `n = 1`: among `0, …, 9` the integers lacking the
digits `0, …, 7` are `8` and `9`, so the count is `2`, while `a(1) = 0`. In general such an
integer has only the digits `8` and `9`, and there are `2^k` of them with `k` digits, so the
count up to `10^n - 1` is `2 + 4 + … + 2^n = 2^(n+1) - 2 = a(n+1)` (checked with python3 for
`1 ≤ n ≤ 7`: 2, 6, 14, 30, 62, 126, 254). `main` states the minimally corrected claim: for
`n ≥ 1`, the count equals `a(n+1)`, i.e. the conjecture with the offset shifted by one.

Conventions. The integer `0` is written with the digit `0`, so it never counts; since
`Nat.digits 10 0 = []`, we require `0 < x` explicitly.

The entry's other conjecture (L. E. Jeffery: for n > 0, a(n) is the least m with
A007814(A000108(m)) = n - 1, proved by P. Schorn in the entry, 2020) is, for `n ≥ 2`, the
statement `statements/oeis-a095121.lean` (A095121(n-1) = 2^n - 2), and is not repeated here.
-/

namespace OMA.S_oeis_a000918

/-- A000918: `a(n) = 2^n - 2`, over the integers (so `a(0) = -1`). -/
def a (n : ℕ) : ℤ := 2 ^ n - 2

/-- The number of integers `x` with `0 ≤ x ≤ 10^n - 1` none of whose decimal digits is one of
`0, 1, …, 7`. -/
def count (n : ℕ) : ℕ :=
  ((Finset.range (10 ^ n)).filter (fun x => 0 < x ∧ ∀ d ∈ Nat.digits 10 x, 7 < d)).card

/-- Wajnberg's conjecture, with the offset corrected by one (see the module docstring). -/
theorem main : ∀ n : ℕ, 1 ≤ n → (count n : ℤ) = a (n + 1) := by
  sorry

end OMA.S_oeis_a000918
