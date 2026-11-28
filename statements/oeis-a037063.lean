import Mathlib

/-!
# A037063: the form of the smallest prime with exactly n digits 5

Source: https://oeis.org/A037063
Credit: @Solfanbtc

A037063 (offset 0): `a(n)` is the smallest prime containing exactly `n` decimal digits `5`.
Data 2, 5, 557, 5557, 155557, 555557, 15555557, 55555553, 3555555551, …

Conjecture (M. F. Hasler, Feb 22 2016): "for all n > 1, a(n) equals [10^(n+1)/9]*50 + b with
1 <= b <= 9 and one of the (first) digits 5 replaced by a 0, 1, 2, 3 or 4."

Reading. `[10^(n+1)/9]*50 = 55…50` has `n + 1` digits 5 (at the positions `10^1, …, 10^(n+1)`)
followed by `0`; adding `b` sets the last digit, and replacing the 5 at position `10^j`
(`1 ≤ j ≤ n + 1`) by `d ∈ {0, …, 4}` subtracts `(5 - d) 10^j`. A leading 5 replaced by 0 gives a
number with one digit fewer, as in `a(2) = 557 = 0557` and `a(7) = 55555553`. `main` states: for
every `n ≥ 2` there are `b ∈ [1, 9]`, `j ∈ [1, n+1]`, `d ∈ [0, 4]` with
`a(n) = 50 (10^(n+1) - 1)/9 + b - (5 - d) 10^j`.

Checked with python3: the listed terms, and the conjecture for `2 ≤ n < 45` (smallest primes
found by exhaustive search over numbers with exactly `n` fives, by increasing length; primality
by Miller-Rabin with the first 12 prime bases, deterministic below about `3·10^24`, probable
above).
-/

namespace OMA.S_oeis_a037063

/-- A037063: the smallest prime with exactly `n` decimal digits `5`. -/
noncomputable def a (n : ℕ) : ℕ := sInf {p : ℕ | p.Prime ∧ (Nat.digits 10 p).count 5 = n}

/-- Hasler's conjecture on the form of `a(n)`, `n ≥ 2`. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    ∃ b j d : ℕ, 1 ≤ b ∧ b ≤ 9 ∧ 1 ≤ j ∧ j ≤ n + 1 ∧ d ≤ 4 ∧
      (a n : ℤ) = 50 * ((10 : ℤ) ^ (n + 1) - 1) / 9 + b - (5 - d) * 10 ^ j := by
  sorry

end OMA.S_oeis_a037063
