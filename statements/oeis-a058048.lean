import Mathlib

/-!
# A058048: For each prime P consider the generalized Collatz sequence of each integer N > 1 defined by c(0) = N, c(m+1) = c(m) * P + 1 if F > P, else c(m+1) = c(m) / F, where F is the smallest factor of c(m), until the sequence cycles. If all c(i) > 1 for some starting number N then P belongs to the sequence (and vice versa).

Source: https://oeis.org/A058048
Credit: @Solfanbtc

Conjecture (OEIS A058048): "Missing primes are as yet only conjectures" (Jeff Heleen checked the
primes < 1000 and start points up to 10^7): the primes P <= 401 (the range of the listed terms)
that are not listed, namely 3, 5, 7, 29, 41, 79, 89, 107, 109, 127, 149, 157, 179, 191, 199, 211,
307, 311, 317, 337, 349, 359, 397, are not in the sequence, i.e. for each of them every starting
number N > 1 reaches c(m) = 1.

Conventions. F is the smallest prime factor of c(m) (`Nat.minFac`); the map is
c ↦ c P + 1 if F > P, and c ↦ c / F otherwise. The listed primes themselves are not restated
(their membership rests on the computations behind the entry).
Checked numerically: for each of the 23 primes and every 2 <= N < 2000 the trajectory reaches 1.
-/

namespace OMA.S_oeis_a058048

/-- One step of the generalized Collatz map for the prime `P`. -/
def step (P c : ℕ) : ℕ := if P < c.minFac then c * P + 1 else c / c.minFac

/-- The primes up to 401 missing from the listed terms. -/
def missingPrimes : Finset ℕ :=
  {3, 5, 7, 29, 41, 79, 89, 107, 109, 127, 149, 157, 179, 191, 199, 211, 307, 311, 317, 337, 349,
   359, 397}

theorem main : ∀ P ∈ missingPrimes, ∀ N : ℕ, 1 < N → ∃ m : ℕ, (step P)^[m] N = 1 := by
  sorry

end OMA.S_oeis_a058048
