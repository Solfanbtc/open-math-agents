import Mathlib

/-!
# A122134: Expansion of Sum_{k>=0} x^(k^2+k)/((1-x)(1-x^2)...(1-x^(2k))).

Source: https://oeis.org/A122134
Credit: @Solfanbtc

Conjecture (Gus Wiseman, Feb 26 2022, OEIS A122134): a(n) is also the number of even-length
integer partitions y of n such that y_i != y_{i+1} for all even i.
Status: the entry says this is proved (Connor, Proposition 3, cited in the entry), so it is a
known result, stated faithfully.

Conventions.
* a(n) is the coefficient of x^n in Σ_k x^(k^2+k) / ((1-x)(1-x^2)...(1-x^(2k))). The coefficient
  of x^m in 1/((1-x)...(1-x^(2k))) is the number of partitions of m into parts <= 2k, so
  a(n) = Σ_{k : k^2+k <= n} #{partitions of n - k^2 - k into parts <= 2k}.
* A partition y = (y_1 >= y_2 >= ... >= y_L) is the decreasingly sorted list of the parts of a
  `Nat.Partition n`; with 0-based list positions, y_i is entry i - 1, so the condition reads:
  entry i - 1 differs from entry i for every even i with 2 <= i < L.
Checked numerically: both descriptions give the 25 listed terms 1, 0, 1, 1, 2, 2, 4, 4, 6, 7, ...
-/

namespace OMA.S_oeis_a122134

/-- a(n), the coefficient of x^n of the generating function. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1),
    if k * k + k ≤ n then
      (Finset.univ.filter fun p : Nat.Partition (n - (k * k + k)) => ∀ x ∈ p.parts, x ≤ 2 * k).card
    else 0

/-- Wiseman's condition on a partition `y` of `n`: even length, and `y_i ≠ y_{i+1}` for even `i`. -/
def WisemanCond {n : ℕ} (p : Nat.Partition n) : Prop :=
  let y := p.parts.sort (· ≥ ·)
  Even y.length ∧ ∀ i : ℕ, Even i → 2 ≤ i → i < y.length → y.getD (i - 1) 0 ≠ y.getD i 0

open Classical in
theorem main : ∀ n : ℕ, a n = (Finset.univ.filter fun p : Nat.Partition n => WisemanCond p).card := by
  sorry

end OMA.S_oeis_a122134
