import Mathlib

/-!
# A089705: Smallest n-digit prime in which the unit place digit is 1 and the k-th most significant digit is prime (2,3,5,7) if k is prime else is composite (4,6,8,9,0).

Source: https://oeis.org/A089705
Credit: @Solfanbtc

Positions are counted from the units digit (position 1), as in C. Ronaldo's Maple program, which
tests the primality of the position from the right. This reading reproduces all the data, e.g.
`a(8) = 42020351`. An admissible `n`-digit number (`n ≥ 2`) has units digit 1, a digit in
{2, 3, 5, 7} at each prime position `2 ≤ k ≤ n`, and a digit in {0, 4, 6, 8, 9} at each composite
position `2 ≤ k ≤ n` (nonzero at the leading position `n`, since it has `n` digits). `a(n)` is the
least admissible prime. Checked with python3: this gives the data for `2 ≤ n ≤ 14`.

Conjecture (A. Murthy): "All the composite positions are occupied by a zero except the most
significant digit, which in most cases perhaps is 4. Most of the prime positions for p > 5 are
occupied by 2." The first sentence is precise and is what `main` states: in `a(n)`, every
composite position `k` with `2 ≤ k < n` holds the digit 0. The hedged remarks ("in most cases
perhaps", "most of the prime positions") are not precise claims and are not formalized. (python3:
true for `2 ≤ n ≤ 14`.)
-/

namespace OMA.S_oeis_a089705

/-- The digit of `x` at position `k` (position 1 = units digit). -/
def digitAt (x k : ℕ) : ℕ := (Nat.digits 10 x).getD (k - 1) 0

/-- Admissible `n`-digit numbers. -/
def Admissible (n x : ℕ) : Prop :=
  10 ^ (n - 1) ≤ x ∧ x < 10 ^ n ∧ digitAt x 1 = 1 ∧
    ∀ k, 2 ≤ k → k ≤ n →
      (k.Prime → digitAt x k ∈ ({2, 3, 5, 7} : Finset ℕ)) ∧
      (¬ k.Prime → digitAt x k ∈ ({0, 4, 6, 8, 9} : Finset ℕ))

theorem main :
    ∀ n x : ℕ, 2 ≤ n → IsLeast {y | Admissible n y ∧ y.Prime} x →
      ∀ k, 2 ≤ k → k < n → ¬ k.Prime → digitAt x k = 0 := by
  sorry

end OMA.S_oeis_a089705
