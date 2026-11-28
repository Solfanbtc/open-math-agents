import Mathlib

/-!
# A104169: Highly decomposable Smith numbers.

Source: https://oeis.org/A104169
Credit: @Solfanbtc

A Smith number (A006753) is a composite `n` whose decimal digit sum equals the sum of the
decimal digit sums of its prime factors counted with multiplicity. A Smith number is highly
decomposable if it sets a record for the number of prime factors counted with multiplicity
(`Ω`): `Ω(m) > Ω(s)` for every Smith number `s < m`. The first one is the first Smith number,
`4`, which trivially sets a record. The definition below reproduces the data up to `2·10^6`
(4, 27, 378, 576, 2688, 17496, 44928, 75776, 168960, 319488, 958464).

Conjecture (S. S. Gupta, OEIS %C): except for 27, all highly decomposable Smith numbers are
even.
-/

namespace OMA.S_oeis_a104169

/-- Decimal digit sum. -/
def digitSum (n : ℕ) : ℕ := (Nat.digits 10 n).sum

/-- Smith number (A006753). -/
def IsSmith (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ digitSum n = (n.primeFactorsList.map digitSum).sum

/-- Highly decomposable Smith number: a Smith number with more prime factors (counted with
multiplicity) than every smaller Smith number. -/
def IsHighlyDecomposableSmith (m : ℕ) : Prop :=
  IsSmith m ∧ ∀ s < m, IsSmith s → s.primeFactorsList.length < m.primeFactorsList.length

theorem main : ∀ m : ℕ, IsHighlyDecomposableSmith m → m ≠ 27 → Even m := by
  sorry

end OMA.S_oeis_a104169
