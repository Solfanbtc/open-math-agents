import Mathlib

/-!
# A119479: Length of longest run of consecutive integers having exactly n divisors.

Source: https://oeis.org/A119479
Credit: @Solfanbtc

Claim (Vladimir Letsko, Jul 18 2016, in the entry): Schinzel's conjecture H would imply that
* a(2p) = 3 for all primes p > 3;
* a(2pq) = 3 for all primes p, q such that gcd(p-1, q-1) > 4;
* a(6p) = 5 for all odd primes p;
* a(n) = 7 for all n > 4 such that n is divisible by 4 and not divisible by 3.
Stated as the implication: Schinzel's Hypothesis H → (the four claims).

Conventions.
* a(n) = the length L of the longest run of consecutive positive integers k, k+1, ..., k+L-1
  each having exactly n divisors (`Nat.divisors`); "a(n) = L" is stated as: L is the greatest
  element of the set of lengths of such runs (so runs of length L exist and none is longer).
  Consistent with the data: a(8) = a(16) = a(20) = 7, a(10) = a(14) = a(22) = 3, a(18) = 5.
* Schinzel's Hypothesis H: for every finite set of irreducible polynomials f ∈ ℤ[X] with
  positive leading coefficients such that no prime divides ∏ f(n) for every integer n, there
  are infinitely many natural numbers n with every f(n) prime. (Irreducibility in ℤ[X]
  includes primitivity, as usual.)
* The second claim is stated literally for all primes p, q (the source does not require
  p ≠ q).
-/

namespace OMA.S_oeis_a119479

open Polynomial

/-- Schinzel's Hypothesis H. -/
def SchinzelH : Prop :=
  ∀ fs : Finset ℤ[X], (∀ f ∈ fs, Irreducible f ∧ 0 < f.leadingCoeff) →
    (∀ p : ℕ, p.Prime → ∃ n : ℤ, ¬ (p : ℤ) ∣ ∏ f ∈ fs, f.eval n) →
    {n : ℕ | ∀ f ∈ fs, Prime (f.eval (n : ℤ))}.Infinite

/-- L is the length of a run of consecutive positive integers with exactly n divisors. -/
def IsRunLength (n L : ℕ) : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ ∀ i < L, (k + i).divisors.card = n

/-- a(n) = L: the longest such run has length L. -/
def LongestRun (n L : ℕ) : Prop := IsGreatest {M : ℕ | IsRunLength n M} L

theorem main : SchinzelH →
    (∀ p : ℕ, p.Prime → 3 < p → LongestRun (2 * p) 3) ∧
    (∀ p q : ℕ, p.Prime → q.Prime → 4 < Nat.gcd (p - 1) (q - 1) → LongestRun (2 * p * q) 3) ∧
    (∀ p : ℕ, p.Prime → p ≠ 2 → LongestRun (6 * p) 5) ∧
    (∀ n : ℕ, 4 < n → 4 ∣ n → ¬ 3 ∣ n → LongestRun n 7) := by
  sorry

end OMA.S_oeis_a119479
