import Mathlib

/-!
# A078124: Second column, M(n+1,1) for n>=0, of infinite lower triangular matrix M defined in A078122.

Source: https://oeis.org/A078124
Credit: @Solfanbtc

A078122: `M` is the infinite lower triangular matrix with `M(k,0) = 1` and `M(k,k) = 1` for all
`k ≥ 0`, and `[M^3](i,j) = M(i+1,j+1)` for all `i, j ≥ 0`. (The entry writes `M(0,k)=1`; its data,
example and programs all take column 0 to be all ones.) These conditions determine `M` row by
row, since `M(i+1, j+1) = ∑_{k,l ≤ i} M(i,k) M(k,l) M(l,j)` only uses rows `≤ i`. Here
`mat i` is the matrix whose rows `0, …, i` are those of `M` (and later rows are 0), and
`M r c = mat r r c`. Checked with python3 (mirroring these definitions): rows 1; 1,1; 1,3,1;
1,12,9,1; 1,93,117,27,1; ... as in A078122.

Conjecture (P. D. Hanna, in the %F line of the entry): `a(n) = M(n+1, 1)` equals the number of
partitions of `2·3^n` into powers of 3, i.e. the coefficient of `x^(2·3^n)` in
`1/∏_{j≥0} (1 - x^(3^j))`. Checked with python3 for `0 ≤ n ≤ 8`
(1, 3, 12, 93, 1632, 68457, 7112055, 1879090014, 1287814075131).
-/

namespace OMA.S_oeis_a078124

/-- `mat i`: rows `0, …, i` of `M`, later rows zero. -/
def mat : ℕ → ℕ → ℕ → ℕ
  | 0 => fun r c => if r = 0 ∧ c = 0 then 1 else 0
  | i + 1 => fun r c =>
    if r ≤ i then mat i r c
    else if r = i + 1 then
      (if c = 0 then 1
       else ∑ k ∈ Finset.range (i + 1), ∑ l ∈ Finset.range (i + 1),
          mat i i k * mat i k l * mat i l (c - 1))
    else 0

/-- The matrix `M` of A078122. -/
def M (r c : ℕ) : ℕ := mat r r c

open Classical in
/-- Number of partitions of `N` into powers of 3. -/
noncomputable def partitionsPow3 (N : ℕ) : ℕ :=
  (Finset.univ.filter (fun p : Nat.Partition N => ∀ x ∈ p.parts, ∃ e : ℕ, x = 3 ^ e)).card

theorem main : ∀ n : ℕ, M (n + 1) 1 = partitionsPow3 (2 * 3 ^ n) := by
  sorry

end OMA.S_oeis_a078124
