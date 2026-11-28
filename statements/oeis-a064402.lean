import Mathlib

/-!
# A064402: Numbers k such that prime(k) + k is prime, where prime(k) is the k-th prime.

Source: https://oeis.org/A064402
Credit: @Solfanbtc

Conjecture (Zak Seidov, OEIS A064402, comment, Nov 10 2013): the first differences include all
even integers.

Conventions:
* prime(k) is the k-th prime, prime(1) = 2, i.e. `Nat.nth Nat.Prime (k - 1)`; the terms are the
  k ≥ 1 with prime(k) + k prime: 1, 2, 4, 6, 18, 22, ...
* "All even integers" means all positive even d (the sequence is increasing). A first
  difference equal to d means two consecutive terms k < k' (no term strictly between) with
  k' - k = d.
* Checked in Python (terms k with prime(k) + k ≤ 3·10^7): the definition reproduces %S; every
  even d < 136 occurs as a difference in that range.
-/

namespace OMA.S_oeis_a064402

/-- `k` is a term: `prime(k) + k` is prime. -/
def IsTerm (k : ℕ) : Prop := 1 ≤ k ∧ (Nat.nth Nat.Prime (k - 1) + k).Prime

/-- Seidov's conjecture: every positive even number is a difference of consecutive terms. -/
theorem main :
    ∀ d : ℕ, 0 < d → Even d →
      ∃ k k' : ℕ, IsTerm k ∧ IsTerm k' ∧ k < k' ∧ k' - k = d ∧
        ∀ j, k < j → j < k' → ¬ IsTerm j := by
  sorry

end OMA.S_oeis_a064402
