import Mathlib

/-!
# A068890: a(1) = 1; a(n) = smallest nontrivial n-th power with property that digits alternate in parity.

Source: https://oeis.org/A068890
Credit: @Solfanbtc

A number has digits alternating in parity when any two adjacent decimal digits have different
parities (a one-digit number qualifies). For `n ≥ 2`, `a(n)` is the smallest `m ^ n` with
`m ≥ 2` (nontrivial: `0 ^ n` and `1 ^ n` excluded) whose digits alternate in parity, when such a
power exists. Data: `a(2..8) = 4, 8, 16, 32, 729, 2187, 256` (checked in Python).

Conjecture (in the entry): the sequence is finite, i.e. for some `n ≥ 2` there is no
nontrivial `n`-th power with digits alternating in parity, so the sequence stops there.

Status: settled. Benjamin Chaffin (comment in the entry, Nov 24 2021) observed that for every
`m`, `m ^ 10 mod 1000` lies in `{0, 1, 24, 49, 176, 201, 224, 249, 376, 401, 424, 449, 576, 601,
624, 625, 649, 776, 801, 824, 849, 976}`; since `m ^ 10 ≥ 1024` for `m ≥ 2`, its last three
digits are one of these (as a three-digit string), none of which alternates in parity, so
`a(10)` does not exist and the sequence is finite.
-/

namespace OMA.S_oeis_a068890

/-- Adjacent decimal digits of `x` have different parities. -/
def AltParity (x : ℕ) : Prop :=
  ∀ i : ℕ, i + 1 < (Nat.digits 10 x).length →
    (Nat.digits 10 x)[i]! % 2 ≠ (Nat.digits 10 x)[i + 1]! % 2

/-- The sequence is finite: some `a(n)`, `n ≥ 2`, does not exist. -/
theorem main : ∃ n : ℕ, 2 ≤ n ∧ ¬ ∃ m : ℕ, 2 ≤ m ∧ AltParity (m ^ n) := by
  sorry

end OMA.S_oeis_a068890
