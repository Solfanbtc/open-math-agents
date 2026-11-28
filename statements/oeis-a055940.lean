import Mathlib

/-!
# A055940: there are infinitely many counterbalanced numbers

Source: https://oeis.org/A055940
Credit: @Solfanbtc

A055940: counterbalanced numbers, the composite numbers `k` such that `phi(k)/(sigma(k) - k)` is
an integer. Data 133, 403, 583, 713, 817, 2077, …

The entry (citing Banks and Luca, 2007): "under Dickson's conjecture this sequence is infinite,
since for each positive integer m, if p = 5m + 1 and q = 20m + 13 are primes, then p*q is a
term." `main` states the implied conjecture: there are infinitely many counterbalanced numbers.
(For composite `k`, `sigma(k) - k ≥ 1`, so the condition is `(sigma(k) - k) ∣ phi(k)`.) Checked
with python3: the definition reproduces the listed terms below 6000, and the family gives e.g.
`m = 2`: `11 · 53 = 583`, a listed term.
-/

namespace OMA.S_oeis_a055940

open ArithmeticFunction

/-- `k` is counterbalanced. -/
def Counterbalanced (k : ℕ) : Prop :=
  1 < k ∧ ¬ k.Prime ∧ (sigma 1 k - k) ∣ k.totient

/-- The conjecture implied by Dickson's conjecture: A055940 is infinite. -/
theorem main : {k : ℕ | Counterbalanced k}.Infinite := by
  sorry

end OMA.S_oeis_a055940
