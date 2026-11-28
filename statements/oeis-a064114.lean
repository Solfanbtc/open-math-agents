import Mathlib

/-!
# A064114: Unitary weird numbers

Source: https://oeis.org/A064114 (see A034683, A293188)
Credit: @Solfanbtc

A unitary divisor of `n` is a divisor `d` with `gcd(d, n/d) = 1`; it is proper when `d < n`.
* `n` is unitary abundant (A034683) when the sum of its proper unitary divisors exceeds `n`
  (equivalently `σ*(n) > 2n`);
* `n` is unitary pseudoperfect (A293188) when `n` is the sum of some set of distinct proper
  unitary divisors of `n`;
* `n` is unitary weird (A064114) when it is unitary abundant but not unitary pseudoperfect:
  70, 4030, 5390, 5830, 10430, ...
(Example: the proper unitary divisors of 70 are 1, 2, 5, 7, 10, 14, 35, with sum 74 > 70, and no
subset of them sums to 70.)

Conjecture (Amiram Eldar, Oct 19 2019): all terms are divisible by 10.

Sanity check (python): these definitions give exactly the 38 listed terms below 22000, all
divisible by 10.
-/

namespace OMA.S_oeis_a064114

/-- The proper unitary divisors of `n`. -/
def properUnitaryDivisors (n : ℕ) : Finset ℕ :=
  n.properDivisors.filter (fun d => Nat.Coprime d (n / d))

/-- `n` is unitary abundant. -/
def IsUnitaryAbundant (n : ℕ) : Prop := n < ∑ d ∈ properUnitaryDivisors n, d

/-- `n` is unitary pseudoperfect. -/
def IsUnitaryPseudoperfect (n : ℕ) : Prop :=
  ∃ s ⊆ properUnitaryDivisors n, ∑ d ∈ s, d = n

/-- Eldar's conjecture: every unitary weird number is divisible by 10. -/
theorem main : ∀ n : ℕ, IsUnitaryAbundant n → ¬ IsUnitaryPseudoperfect n → 10 ∣ n := by
  sorry

end OMA.S_oeis_a064114
