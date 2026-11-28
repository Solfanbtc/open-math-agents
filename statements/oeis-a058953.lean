import Mathlib

/-!
# A058953: Numbers k = p*2^x (p prime, x ≥ 0) with tau(k) - m = A058933(k), m ∈ {0, 1}.

Source: https://oeis.org/A058953
Credit: @Solfanbtc

The terms are the k = p·2^x (p prime, x ≥ 0) such that tau(k) - m = A058933(k) for m = 0 or 1.
The entry: "(p = 2 => m = 1); (Conjecture: [for p > 2]; if p = A040069 then m = 0 else m = 1.)"
That is: for a term k = p·2^x with p an odd prime, m = 0 (tau(k) = A058933(k)) iff p is in
A040069, the primes p such that x^3 = 15 has a solution mod p.

Conventions.
* tau(k) = number of divisors; A058933(n) = number of j with 1 ≤ j ≤ n and Ω(j) = Ω(n), where
  Ω = number of prime factors with multiplicity (`ArithmeticFunction.cardFactors`).
* For odd p the representation k = p·2^x is unique, so m = tau(k) - A058933(k) ∈ {0, 1} is
  determined by k.
* "x^3 = 15 has a solution mod p": ∃ y : ZMod p, y^3 = 15.
* python3 (k < 1.9·10^6): the terms are 2, 3, 10, 28, 176, 832, 4352, 19456, 47104, 1900544
  (the data), with m = 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, and for p = 3, 5, 7, 11, 13, 17, 19, 23, 29
  the cube-root condition holds exactly when m = 0 (it fails for 13 and 19).
-/

namespace OMA.S_oeis_a058953

open ArithmeticFunction

/-- A058933: number of j ≤ n with the same number of prime factors (with multiplicity). -/
def A058933 (n : ℕ) : ℕ := ((Finset.Icc 1 n).filter fun j => cardFactors j = cardFactors n).card

/-- tau: number of divisors. -/
def tau (n : ℕ) : ℕ := n.divisors.card

theorem main : ∀ p x : ℕ, p.Prime → p ≠ 2 →
    (tau (p * 2 ^ x) = A058933 (p * 2 ^ x) ∨ tau (p * 2 ^ x) = A058933 (p * 2 ^ x) + 1) →
    (tau (p * 2 ^ x) = A058933 (p * 2 ^ x) ↔ ∃ y : ZMod p, y ^ 3 = 15) := by
  sorry

end OMA.S_oeis_a058953
