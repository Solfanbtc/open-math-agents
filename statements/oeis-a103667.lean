import Mathlib

/-!
# A103667: Primes p such that the largest prime divisor of p-1 is greater than the largest prime divisor of p+1.

Source: https://oeis.org/A103667
Credit: @Solfanbtc

Conjecture (Charles R Greathouse IV, Dec 22 2022): "this sequence is of positive relative
density in the primes, perhaps even 1/2."

Formalization.
* `P n` is the largest prime factor of `n` (`0` for `n = 1`, which has none, so `p = 2` is not a
  term: P(1) = 0 < P(3) = 3); `InSeq p` : `p` prime and `P(p-1) > P(p+1)`. This reproduces the
  data 7, 11, 23, 29, 31, 47, ... (python3).
* "of positive relative density in the primes": the relative density
  `lim #{p ≤ x : InSeq p} / #{p ≤ x : p prime}` exists and is positive. The hedged addition
  "perhaps even 1/2" is not part of the statement. (python3: the proportion up to 2*10^6 is
  about 0.5004.)
-/

namespace OMA.S_oeis_a103667

/-- Largest prime factor (`0` if there is none). -/
def P (n : ℕ) : ℕ := n.primeFactors.sup id

/-- `p` is a term of A103667. -/
def InSeq (p : ℕ) : Prop := p.Prime ∧ P (p + 1) < P (p - 1)

instance : DecidablePred InSeq := fun p => by unfold InSeq; infer_instance

theorem main :
    ∃ d : ℝ, 0 < d ∧
      Filter.Tendsto
        (fun x : ℕ => (((Finset.range (x + 1)).filter InSeq).card : ℝ) /
          ((Finset.range (x + 1)).filter Nat.Prime).card)
        Filter.atTop (nhds d) := by
  sorry

end OMA.S_oeis_a103667
