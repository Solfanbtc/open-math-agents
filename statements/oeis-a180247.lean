import Mathlib

/-!
# A180247: Prime Brier numbers: primes p such that for all k >= 1 the numbers p*2^k + 1 and p*2^k - 1 are composite.

Source: https://oeis.org/A180247
Credit: @Solfanbtc

A prime Brier number is a prime `p` such that for every `k ≥ 1` both `p·2^k + 1` and `p·2^k - 1`
are composite. (Both numbers are at least 3 for a prime `p` and `k ≥ 1`, so "composite" is the
same as "not prime".)

Conjecture (A. Wesolowski, Feb 03 2016, OEIS A180247): every prime Brier number has more than
11 digits, i.e. is at least `10^11`. (He reports there are none below `10^10`, and for every
prime `p < 10^11` some `p·2^k ± 1` has all prime factors above 1321, so no covering set with
primes up to 1321 works; the smallest known prime Brier number has 23 digits.)
-/

namespace OMA.S_oeis_a180247

/-- `p` is a prime Brier number. -/
def IsPrimeBrier (p : ℕ) : Prop :=
  p.Prime ∧ ∀ k : ℕ, 1 ≤ k → ¬ (p * 2 ^ k + 1).Prime ∧ ¬ (p * 2 ^ k - 1).Prime

/-- Conjecture: every prime Brier number has more than 11 decimal digits. -/
theorem main : ∀ p : ℕ, IsPrimeBrier p → 10 ^ 11 ≤ p := by
  sorry

end OMA.S_oeis_a180247
