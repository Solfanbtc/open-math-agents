import Mathlib

/-!
# A087331: Smallest number with all identical digits having n distinct prime divisors.

Source: https://oeis.org/A087331
Credit: @Solfanbtc

OEIS comment (Robert G. Wilson v): "The conjecture that 'for n > 2, a(n) == 0 (mod 3)' is not
true since a(12) = 32 2's which is == 1 (mod 3)."

So the claim recorded by the entry is a *refutation*: the conjecture `∀ n > 2, a(n) ≡ 0 (mod 3)`
is false, the witness being a(12) = 22...2 (32 digits), which is ≡ 2 * 32 ≡ 1 (mod 3).
This is a settled (disproved) conjecture; we state it faithfully together with all terms listed
in the entry's data section (%S/%T/%U, offset 0, n = 0..14).

Conventions.
* A "number with all identical digits" (repdigit, base 10) is `d * (10^k - 1) / 9` with a
  digit `1 ≤ d ≤ 9` and a length `k ≥ 1`; in particular `a(0) = 1` (1 has no prime divisor),
  matching the data.
* "n distinct prime divisors" is `m.primeFactors.card = n` (ω(m) = n).
* `a n` is the least such repdigit, as an `sInf` (which would be `0` if none existed; the
  listed terms show the sets are nonempty for n ≤ 14).

The terms were checked with python3 by factoring every repdigit with at most 32 digits.
-/

namespace OMA.S_oeis_a087331

/-- `m` is a base-10 repdigit: `k ≥ 1` copies of a nonzero digit `d`. -/
def IsRepdigit (m : ℕ) : Prop :=
  ∃ d k : ℕ, 1 ≤ d ∧ d ≤ 9 ∧ 1 ≤ k ∧ m = d * ((10 ^ k - 1) / 9)

/-- A087331(n): the smallest repdigit with exactly `n` distinct prime divisors. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | IsRepdigit m ∧ m.primeFactors.card = n}

theorem main :
    (a 0 = 1 ∧ a 1 = 2 ∧ a 2 = 6 ∧ a 3 = 66 ∧ a 4 = 6666 ∧ a 5 = 111111 ∧ a 6 = 222222 ∧
      a 7 = 111111111111 ∧ a 8 = 222222222222 ∧ a 9 = 222222222222222222 ∧
      a 10 = 111111111111111111111111 ∧ a 11 = 222222222222222222222222 ∧
      a 12 = 22222222222222222222222222222222 ∧ a 13 = 111111111111111111111111111111 ∧
      a 14 = 222222222222222222222222222222) ∧
    a 12 = 2 * ((10 ^ 32 - 1) / 9) ∧ a 12 % 3 = 1 ∧
    ¬ (∀ n : ℕ, n > 2 → a n % 3 = 0) := by
  sorry

end OMA.S_oeis_a087331
