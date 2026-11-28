import Mathlib

/-!
# A129759: Largest prime factor of Landau's function L(n)

Source: https://oeis.org/A129759
Credit: @Solfanbtc

`L(n)` (A000793, Landau's function) is the largest order of a permutation of `n` elements, and
`a(n)` (offset 1) is the largest prime factor of `L(n)`: `1, 2, 3, 2, 3, 3, 3, 5, 5, …` (for
`n = 1`, `L(1) = 1` and the entry sets `a(1) = 1`; below the largest prime factor of `1` is `0`,
which only concerns `n = 1`, outside the range of the conjecture). A Python computation of `L(n)`
reproduces all 80 data terms.

Known: `a(n) ~ √(n log n)` (Nicolas); `a(n) ≤ 1.328 √(n log n)` for `n > 4` (Grantham).
Conjecture (Massias, Nicolas & Robin, recorded by Charles R Greathouse IV, Jun 02 2014):
`a(n) ≤ 1.265… √(n log n)` for `n > 4`, with equality at `n = 215`. The constant is the value of
`a(n)/√(n log n)` at `n = 215` (`a(215) = 43`, `43/√(215 log 215) = 1.26542…`), so the claim is
stated as `a(n)/√(n log n) ≤ a(215)/√(215 log 215)` for all `n > 4`. (Python: true for
`5 ≤ n ≤ 3000`, the maximum being attained only at `n = 215`.)
-/

namespace OMA.S_oeis_a129759

/-- Landau's function: the largest order of a permutation of `Fin n`. -/
noncomputable def L (n : ℕ) : ℕ := Finset.univ.sup fun σ : Equiv.Perm (Fin n) => orderOf σ

/-- A129759 (for `n ≥ 2`): the largest prime factor of `L(n)`. -/
noncomputable def a (n : ℕ) : ℕ := (L n).primeFactors.sup id

/-- Massias–Nicolas–Robin: `a(n) / √(n log n) ≤ a(215) / √(215 log 215)` for `n > 4`. -/
theorem main : ∀ n : ℕ, 4 < n →
    (a n : ℝ) / Real.sqrt (n * Real.log n) ≤ (a 215 : ℝ) / Real.sqrt (215 * Real.log 215) := by
  sorry

end OMA.S_oeis_a129759
