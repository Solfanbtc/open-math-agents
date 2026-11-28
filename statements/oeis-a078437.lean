import Mathlib

/-!
# A078437: Decimal expansion of sum of alternating series of reciprocals of primes.

Source: https://oeis.org/A078437
Credit: @Solfanbtc

Conjecture (Simon Cavegn, OEIS A078437, comment, Apr 18 2026): the next terms are
a(14)-a(18) = 4, 5, 9, 4, 8. (This contains Robert Price's earlier "most likely a(14)=4 and
a(15)=5", Sep 13 2011.) With the listed terms a(0)-a(13) = 2,6,9,6,0,6,3,5,1,9,7,1,6,7 this says
that the first 19 decimals of the constant are 0.2696063519716745948.

Conventions:
* The constant is S = Sum_{j>=1} (-1)^(j+1)/prime(j) = 1/2 - 1/3 + 1/5 - 1/7 + ... The series
  converges only conditionally (Leibniz), so S is defined as the limit of the partial sums
  f(k) = Sum_{j=1..k} (-1)^(j+1)/prime(j) (Lean's `tsum` would give 0 for a non-summable
  series). The statement asserts that the limit exists (true by the alternating series test)
  and fixes its digits.
* Offset 0 for a constant below 1: a(0) is the first digit after the decimal point, so the
  digits a(0..18) are those of `⌊S * 10^19⌋ = 2696063519716745948`.
* Schoenfield's smoothed partial sums h(2^m) in the entry approach 0.26960635197167459485...,
  consistent with these digits.
-/

namespace OMA.S_oeis_a078437

open Filter Topology

/-- The partial sum `f(k) = Σ_{j=1..k} (-1)^(j+1) / prime(j)`. -/
noncomputable def f (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, (-1 : ℝ) ^ j / (Nat.nth Nat.Prime j : ℝ)

/-- The first 19 decimals of `1/2 - 1/3 + 1/5 - 1/7 + ...` are `2696063519716745948`. -/
theorem main :
    ∃ S : ℝ, Tendsto f atTop (𝓝 S) ∧ ⌊S * 10 ^ 19⌋ = 2696063519716745948 := by
  sorry

end OMA.S_oeis_a078437
