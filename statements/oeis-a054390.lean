import Mathlib

/-!
# A054390: Ways of writing n as a sum of powers of 3, each power used at most three times

Source: https://oeis.org/A054390
Credit: @Solfanbtc

`a(n)` (offset 0) is the number of ways of writing `n = ∑_j c_j 3^j` with `0 ≤ c_j ≤ 3`:
`1, 1, 1, 2, 1, 1, 2, 1, 1, 3, …` (g.f. `∏_{j ≥ 0} (1 + x^(3^j) + x^(2·3^j) + x^(3·3^j))`). Only
`3^j ≤ n` can be used, so `j ≤ n` suffices; below a representation is `c : Fin (n+1) → Fin 4`.

A038754: `b(2i) = 3^i`, `b(2i+1) = 2·3^i`: `1, 2, 3, 6, 9, 18, 27, …` (all distinct).

Conjecture (R. J. Mathar, Mar 01 2023, OEIS comment): `a(n)` is the number of ways of partitioning
`n` into distinct parts of A038754, i.e. the number of sets of terms of A038754 with sum `n`. Parts
are `≤ n` and `b(i) > n` for `i > 2n` (`b(i) ≥ 3^(i/2)`), so indices `i ≤ 2n` suffice; a set of parts is a set of indices
(`b` is injective). Python: holds for `n ≤ 400`.
-/

namespace OMA.S_oeis_a054390

/-- A038754: `b(2i) = 3^i`, `b(2i+1) = 2·3^i`. -/
def b (i : ℕ) : ℕ := (1 + i % 2) * 3 ^ (i / 2)

/-- A054390: representations `n = ∑ c_j 3^j` with digits `0 ≤ c_j ≤ 3`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun c : Fin (n + 1) → Fin 4 => ∑ j, (c j : ℕ) * 3 ^ (j : ℕ) = n).card

/-- Partitions of `n` into distinct parts of A038754. -/
def distinctParts (n : ℕ) : ℕ :=
  ((Finset.range (2 * n + 1)).powerset.filter fun S => ∑ i ∈ S, b i = n).card

/-- Mathar's conjecture: `a(n)` counts the partitions of `n` into distinct parts of A038754. -/
theorem main : ∀ n : ℕ, a n = distinctParts n := by
  sorry

end OMA.S_oeis_a054390
