import Mathlib

/-!
# A067590: Number of partitions of n into odious numbers (A000069).

Source: https://oeis.org/A067590
Credit: @Solfanbtc

Odious numbers (A000069) are the `k ≥ 1` with an odd number of 1's in their binary expansion
(`1, 2, 4, 7, 8, 11, ...`). `a(n)` (`n ≥ 0`) is the number of partitions of `n` into odious
parts: `1, 1, 2, 2, 4, 4, 6, 7, 11, ...`.

Conjecture (Vaclav Kotesovec, Jul 06 2025, in the entry):
`a(n) ~ c · exp(π √(n/3)) / n^(5/8)`, where `c = 0.221864833...`.

The constant is only given by its decimal digits, so the statement is: there is a constant `c`
with decimal expansion beginning `0.221864833` (i.e. `0.221864833 ≤ c < 0.221864834`) such that
`a(n)` is asymptotically equivalent to `c · exp(π √(n/3)) / n^(5/8)`. (Such a `c` is unique,
being the limit of the ratio.)

A python3 check (exact partition counts up to `n = 12000`): the definition reproduces the data,
and `a(n) / (exp(π √(n/3)) / n^(5/8))` is `0.22113, 0.22134, 0.22150, 0.22160, 0.22165` at
`n = 1000, 2000, 4000, 8000, 12000`, increasing slowly towards the stated value.
-/

namespace OMA.S_oeis_a067590

open Filter Asymptotics

/-- `k` is odious: an odd number of 1's in base 2. -/
def Odious (k : ℕ) : Prop := Odd (Nat.digits 2 k).sum

instance : DecidablePred Odious := fun k => by unfold Odious; infer_instance

/-- `a(n)`: the number of partitions of `n` into odious parts. -/
def a (n : ℕ) : ℕ := (Nat.Partition.restricted n Odious).card

/-- Kotesovec's conjecture: `a(n) ~ c exp(π √(n/3)) / n^(5/8)` with `c = 0.221864833...`. -/
theorem main : ∃ c : ℝ, (0.221864833 : ℝ) ≤ c ∧ c < 0.221864834 ∧
    (fun n : ℕ => (a n : ℝ)) ~[atTop]
      (fun n : ℕ => c * Real.exp (Real.pi * Real.sqrt ((n : ℝ) / 3)) / (n : ℝ) ^ ((5 : ℝ) / 8)) := by
  sorry

end OMA.S_oeis_a067590
