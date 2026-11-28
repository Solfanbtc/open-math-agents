import Mathlib

/-!
# A054688: C(n^2+n-1, n) is the sum over shapes λ ⊢ n of the squared numbers of SSYT

Source: https://oeis.org/A054688
Credit: @Solfanbtc

A054688 (offset 0): the number of nonnegative integer `n × n` matrices with sum of entries `n`;
`a(n) = binomial(n^2 + n - 1, n)`. Data 1, 1, 10, 165, 3876, 118755, …

Conjecture (W. Meeussen, Feb 02 2025): "a(n) equals the sum of squares of the number of
semistandard Young tableaux over all partitions of n."

Reading. The number of semistandard Young tableaux of a shape is finite only once the entries are
bounded; we read it, as the matrix interpretation suggests, with entries in `{1, …, n}` (the
`n × n` matrices). With this reading the statement is the Robinson-Schensted-Knuth
correspondence (matrices with entries summing to `n`, rows and columns indexed by `[n]`,
correspond to pairs of SSYT of the same shape `λ ⊢ n` with entries in `[n]`), so it is a theorem;
the entry still lists it as a conjecture. Example: `n = 2`, shapes `(2)` and `(1,1)` carry 3 and 1
tableaux, `3^2 + 1^2 = 10`.

Definitions. Shapes are Mathlib's `YoungDiagram`s with `n` cells; tableaux are
`SemistandardYoungTableau μ` (weakly increasing rows, strictly increasing columns) whose entries
on the cells of `μ` lie in `[1, n]`. The sum is a `finsum` over the finitely many such shapes.
-/

namespace OMA.S_oeis_a054688

/-- The number of semistandard Young tableaux of shape `μ` with entries in `{1, …, n}`. -/
noncomputable def numSSYT (μ : YoungDiagram) (n : ℕ) : ℕ :=
  {T : SemistandardYoungTableau μ | ∀ i j, (i, j) ∈ μ → 1 ≤ T i j ∧ T i j ≤ n}.ncard

/-- Meeussen's conjecture: `binomial(n^2 + n - 1, n) = Sum_{λ ⊢ n} (number of SSYT of shape λ
with entries in [n])^2`. -/
theorem main : ∀ n : ℕ,
    (n ^ 2 + n - 1).choose n = ∑ᶠ (μ : YoungDiagram) (_ : μ.cells.card = n), numSSYT μ n ^ 2 := by
  sorry

end OMA.S_oeis_a054688
