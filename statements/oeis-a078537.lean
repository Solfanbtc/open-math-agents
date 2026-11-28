import Mathlib

/-!
# A078537: Number of partitions of 4^n into powers of 4 (without regard to order).

Source: https://oeis.org/A078537
Credit: @Solfanbtc

A078537(n) is the number of partitions of `4^n` into powers of `4` (`1, 2, 6, 46, 1086, …`).

A078536 is the infinite lower triangular matrix `M` with `M(k,0) = 1` and `M(k,k) = 1` for all
`k`, and `[M^4](i,j) = M(i+1,j+1)` for all `i, j`. (The entry writes `M(0,k) = 1`, but its data
and example show the first column of `1`'s, and `M(0,k) = 1` for `k > 0` would contradict lower
triangularity, so this is read as `M(k,0) = 1`.) Since `M` is lower triangular, `[M^4](i,j)`
only involves rows `0..i`, so `M(i+1, j+1) = Σ_{a,b,c ≤ i} M(i,a) M(a,b) M(b,c) M(c,j)`
determines `M` row by row from `M(0,0) = 1`. `Mupto n` is `M` restricted to rows `0..n` (`0`
elsewhere), and `M i j = Mupto i i j`. The diagonal condition `M(k,k) = 1` then holds
automatically: `M(i+1,i+1) = M(i,i)^4`.

Conjecture (entry, also stated in A078536): `a(n)` is the sum of row `n` of A078536, i.e.
`Σ_{k=0}^n M(n,k)` equals the number of partitions of `4^n` into powers of `4`. Checked with
python3: the recursion reproduces the data of A078536 (rows 0..8), and the row sums equal the
partition counts for `n ≤ 7` and the listed terms of A078537 for `n ≤ 11`.
-/

namespace OMA.S_oeis_a078537

/-- The matrix `M` of A078536 restricted to rows `0..n` (entries outside are `0`). -/
def Mupto : ℕ → ℕ → ℕ → ℕ
  | 0 => fun i j => if i = 0 ∧ j = 0 then 1 else 0
  | n + 1 => fun i j =>
    if i ≤ n then Mupto n i j
    else if i = n + 1 then
      (if j = 0 then 1 else
        ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1), ∑ c ∈ Finset.range (n + 1),
          Mupto n n a * Mupto n a b * Mupto n b c * Mupto n c (j - 1))
    else 0

/-- A078536: `M(i, j)`. -/
def M (i j : ℕ) : ℕ := Mupto i i j

/-- The conjecture: the row sums of A078536 count partitions of `4^n` into powers of `4`. -/
theorem main : ∀ n : ℕ, ∑ k ∈ Finset.range (n + 1), M n k =
    Nat.card {p : Nat.Partition (4 ^ n) // ∀ i ∈ p.parts, ∃ k : ℕ, i = 4 ^ k} := by
  sorry

end OMA.S_oeis_a078537
