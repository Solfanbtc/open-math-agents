import Mathlib

/-!
# A078122: Infinite lower triangular matrix, M, that satisfies [M^3](i,j) = M(i+1,j+1) for all i,j>=0 where [M^n](i,j) denotes the element at row i, column j, of the n-th power of matrix M, with M(0,k)=1 and M(k,k)=1 for all k>=0.

Source: https://oeis.org/A078122
Credit: @Solfanbtc

`M` is lower triangular with `M(k,0) = 1` (the name's "M(0,k) = 1" must be read as the first
column, as the data and the programs of the entry show) and `M(k,k) = 1`, and
`M(i+1,j+1) = [M^3](i,j)`. Since `M` is lower triangular,
`[M^3](i,j) = Σ_{k ≤ i} Σ_{l ≤ i} M(i,k) M(k,l) M(l,j)`, so this determines `M` row by row:
this is the recursion of the Maple and Mathematica programs of the entry, used below as the
definition. We checked that it reproduces all terms of %S, %T, %U (rows 0..8).

Conjectures (from the entry), checked for `n ≤ 8`:
1. the sum of row `n` equals the number of partitions of `3^n` into powers of 3 (A078125);
2. for all `n > 0` and `0 ≤ k < n`, `M(n,k)` is the coefficient of `x^(3^n - 3^(n-k))` in
   `1 / Π_{j=0..n-k} (1 - x^(3^j))`.
-/

namespace OMA.S_oeis_a078122

/-- The matrix `M`: lower triangular, first column and diagonal 1,
`M(i+1, j+1) = [M^3](i, j)`. -/
def M : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | i + 1, j + 1 =>
      if i < j then 0
      else if j = i then 1
      else ∑ k : Fin (i + 1), ∑ l : Fin (i + 1), M i k * M k l * M l j
termination_by i => i
decreasing_by all_goals omega

/-- Number of partitions of `N` into powers of 3 (A078125 for `N = 3^n`). -/
def powThreePartitions (N : ℕ) : ℕ :=
  ((Finset.univ : Finset (Nat.Partition N)).filter fun p => ∀ i ∈ p.parts, ∃ j ≤ i, i = 3 ^ j).card

/-- Both conjectures of the entry. -/
theorem main :
    (∀ n : ℕ, ∑ k ∈ Finset.range (n + 1), M n k = powThreePartitions (3 ^ n)) ∧
    (∀ n k : ℕ, 0 < n → k < n →
      (M n k : ℚ) = PowerSeries.coeff (3 ^ n - 3 ^ (n - k))
        (∏ j ∈ Finset.range (n - k + 1), (1 - PowerSeries.X ^ (3 ^ j) : PowerSeries ℚ))⁻¹) := by
  sorry

end OMA.S_oeis_a078122
