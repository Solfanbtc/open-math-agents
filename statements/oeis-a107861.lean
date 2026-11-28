import Mathlib

/-!
# A107861: Number of distinct values taken by the sums of all subsets of the n-th roots of unity.

Source: https://oeis.org/A107861
Credit: @Solfanbtc

`a(n)` (offset 1) is the number of distinct complex numbers `Σ_{j ∈ S} ζ_n^j` over all subsets
`S ⊆ {0, ..., n-1}`, with `ζ_n = e^{2πi/n}` (the empty subset gives 0, so `a(1) = 2`).

Conjecture (T. D. Noe, OEIS %C): David W. Wilson's conjectured formula for A103314 may apply
to this sequence too. That formula, A103314 %F (May 08 2005), is
`a(n) = a(s(n))^(n/s(n))`, where `s(n)` (A007947) is the squarefree kernel of `n`.
The data are consistent with it: `a(4) = 3^2`, `a(9) = 7^3`, `a(12) = 19^2`, `a(18) = 19^3`,
`a(20) = 211^2`, `a(25) = 31^5`, `a(27) = 7^9`, `a(28) = 2059^2`, `a(32) = 3^16`.
Stated for every `n ≥ 1`.
-/

namespace OMA.S_oeis_a107861

open Complex

/-- A107861(n): the number of distinct subset sums of the `n`-th roots of unity. -/
noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Finset (Fin n))).image
    (fun S : Finset (Fin n) => ∑ j ∈ S, exp (2 * Real.pi * I * (((j : ℕ) : ℂ)) / n))).card

/-- The squarefree kernel `s(n)` (A007947): the product of the distinct primes dividing `n`. -/
def rad (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

theorem main : ∀ n : ℕ, 1 ≤ n → a n = a (rad n) ^ (n / rad n) := by
  sorry

end OMA.S_oeis_a107861
