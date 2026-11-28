import Mathlib

/-!
# A138004: Odd numbers k for which all nontrivial cycles of the Ducci map on k-tuples modulo 2 have the same length.

Source: https://oeis.org/A138004
Credit: @Solfanbtc

Claim (entry comment): all terms of this sequence are prime numbers.

Conventions. The Ducci map on k-tuples modulo 2 is D(x)_i = x_i + x_(i+1) (indices mod k), on
(ZMod 2)^k. Its cycles are the orbits of its periodic points; the only fixed point is 0, and
the trivial cycle is {0}, so the nontrivial cycles are the orbits of the nonzero periodic points,
and a cycle's length is the minimal period of any of its points. k is a term when k is odd, D has
a nontrivial cycle, and all nontrivial cycles have the same length. The existence clause is the
minimal fix for k = 1: there D(x) = x + x = 0 has no nontrivial cycle, and the vacuous reading
would make 1 a term, but the sequence starts at 3. For odd k ≥ 3 nontrivial cycles always exist
(D is invertible on the nonzero even-weight tuples). A brute-force python check over all 2^k
tuples gives exactly 3, 5, 7, 11, 13, 19 among the odd k ≤ 21, as listed.

Statement: every odd k with this property is prime.
-/

namespace OMA.S_oeis_a138004

/-- The Ducci map on k-tuples modulo 2. -/
def ducci (k : ℕ) (x : Fin k → ZMod 2) : Fin k → ZMod 2 := fun i => x i + x (finRotate k i)

/-- All nontrivial cycles of the Ducci map have the same length (and there is one). -/
def SameCycleLengths (k : ℕ) : Prop :=
  (∃ x ∈ Function.periodicPts (ducci k), x ≠ 0) ∧
    ∀ x ∈ Function.periodicPts (ducci k), ∀ y ∈ Function.periodicPts (ducci k), x ≠ 0 → y ≠ 0 →
      Function.minimalPeriod (ducci k) x = Function.minimalPeriod (ducci k) y

theorem main : ∀ k : ℕ, Odd k → SameCycleLengths k → k.Prime := by
  sorry

end OMA.S_oeis_a138004
