import Mathlib

/-!
# A291698: a(n) = [x^n] Product_{k>=1} (1 + n*x^k).

Source: https://oeis.org/A291698
Credit: @Solfanbtc

Conjecture (Vaclav Kotesovec, Sep 15 2017, in the entry):
a(n) ~ exp(sqrt(2*(log(n)^2 + Pi^2/3)*n)) * (log(n)^2 + Pi^2/3)^(1/4) / (sqrt(Pi) * (2*n)^(5/4)).

Conventions.
* Expanding the product, [x^n] ∏_{k ≥ 1} (1 + n x^k) = ∑ n^(number of parts) over the
  partitions of n into distinct parts (Peter Bala's comment in the entry: each part can be
  coloured in n ways). This is the definition used below; it gives a(0) = 1 (empty partition,
  0^0 = 1), a(1) = 1, a(2) = 2, a(3) = 12, a(6) = 294 as listed.
* `~` is asymptotic equivalence as n → ∞ (`Asymptotics.IsEquivalent` along `atTop`); log is
  the natural logarithm.
-/

namespace OMA.S_oeis_a291698

open Real Filter Asymptotics

/-- A291698: the sum of `n ^ (number of parts)` over partitions of `n` into distinct parts. -/
def a (n : ℕ) : ℕ :=
  ∑ p ∈ (Finset.univ : Finset (Nat.Partition n)).filter (fun p => p.parts.Nodup),
    n ^ p.parts.card

theorem main :
    (fun n : ℕ => (a n : ℝ)) ~[atTop] fun n : ℕ =>
      exp (√(2 * (log n ^ 2 + π ^ 2 / 3) * n)) * (log n ^ 2 + π ^ 2 / 3) ^ ((1 : ℝ) / 4) /
        (√π * (2 * n) ^ ((5 : ℝ) / 4)) := by
  sorry

end OMA.S_oeis_a291698
