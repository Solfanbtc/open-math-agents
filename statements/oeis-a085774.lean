import Mathlib

/-!
# A085774: Numbers k such that (k / sum of digits of k) and (k+1 / sum of digits of k+1) are both semiprime.

Source: https://oeis.org/A085774
Credit: @Solfanbtc

`k` qualifies (A085772) when the digit sum `s(k)` divides `k` and `k / s(k)` is a semiprime
(exactly two prime factors with multiplicity, `bigomega = 2`, as in the PARI program).
A085774 lists the `k ≥ 1` such that both `k` and `k + 1` qualify. This reproduces every term
of %S, %T, %U (Python).

Conjecture (Jason Earls, in the entry): the sequence is infinite.
-/

namespace OMA.S_oeis_a085774

/-- `k / s(k)` is an integer and a semiprime (A085772). -/
def Good (k : ℕ) : Prop :=
  0 < k ∧ (Nat.digits 10 k).sum ∣ k ∧ (k / (Nat.digits 10 k).sum).primeFactorsList.length = 2

theorem main : {k : ℕ | Good k ∧ Good (k + 1)}.Infinite := by
  sorry

end OMA.S_oeis_a085774
