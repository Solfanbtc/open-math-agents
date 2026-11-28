import Mathlib

/-!
# A133306: a(n) = (1/n)*Sum_{i=0..n-1} C(n,i)*C(n,i+1)*5^i*6^(n-i), a(0)=1.

Source: https://oeis.org/A133306 (Philippe Deléham, 2007; conjecture by R. J. Mathar,
May 23 2014; OEIS Foundation, CC BY-SA 4.0).
Credit: @Solfanbtc

Conjecture (OEIS): (n+1)*a(n) + 11*(-2*n+1)*a(n-1) + (n-2)*a(n-2) = 0.

Formalization notes.
* a(n) is defined exactly as in the name of the entry, over ℚ (so the factor 1/n is an exact
  division; the values are the integers listed in the entry).
* The recurrence involves a(n-2), so it is stated for n ≥ 2, the range where all its terms are
  defined (the offset is 0).
* A python computation confirms the 20 listed terms and the recurrence for 2 ≤ n < 300.
-/

namespace OMA.S_oeis_a133306

/-- a(n) = (1/n) Σ_{i=0}^{n-1} C(n,i) C(n,i+1) 5^i 6^(n-i) for n ≥ 1, and a(0) = 1. -/
def a (n : ℕ) : ℚ :=
  if n = 0 then 1 else
    (1 / (n : ℚ)) * ∑ i ∈ Finset.range n,
      ((n.choose i : ℚ) * (n.choose (i + 1) : ℚ) * 5 ^ i * 6 ^ (n - i))

theorem main : ∀ n : ℕ, 2 ≤ n →
    ((n : ℚ) + 1) * a n + 11 * (-2 * (n : ℚ) + 1) * a (n - 1) + ((n : ℚ) - 2) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a133306
