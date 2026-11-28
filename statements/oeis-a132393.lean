import Mathlib

/-!
# A132393: Triangle of unsigned Stirling numbers of the first kind (see A048994), read by rows, T(n,k) for 0 <= k <= n.

Source: https://oeis.org/A132393
Credit: @Solfanbtc

Conjecture (Mikhail Kurkov, May 24 2026, in the %F lines): for all `n, m ≥ 0`,

  T(n+m+1, m+1) = (n+m)! * (Product_{i=1..m} (n+i)^i)
    * Sum_{j_1=0..n} Sum_{j_2=0..j_1} ... Sum_{j_m=0..j_{m-1}}
        (-1)^(n*m + j_1 + ... + j_m) * (Product_{1 <= q < p <= m} (j_q - j_p + p - q)^2)
        * Product_{t=1..m} (n+t-1)_{j_t} / ((n - j_t + t)^(m+1) * (j_t + m - t)!)

where `(x)_{k} = Product_{i=0..k-1} (x - i)` is the falling factorial.

Formalization:
* `T(n, k)` is Mathlib's unsigned Stirling number of the first kind `Nat.stirlingFirst n k`.
* The nested sums range over the tuples `n ≥ j_1 ≥ j_2 ≥ … ≥ j_m ≥ 0`; we index them from `0`,
  as `j : Fin m → ℕ` with every value `≤ n` and `j` antitone (`j 0 = j_1`, …). With this shift
  the 1-based index `t` becomes `t + 1`, so `(n+t-1)_{j_t}` is `Nat.descFactorial (n + t) (j t)`
  (for natural `x`, `Nat.descFactorial x k = x (x-1) ⋯ (x-k+1)`, which is `0` when `k > x`,
  exactly as the product formula), `n - j_t + t` is `n - j t + t + 1` and `j_t + m - t` is
  `j t + (m - 1 - t)`; the differences `p - q` are unchanged.
* `(n+m)! * Product_{i=1..m} (n+i)^i` is written as `(n+m)! * ∏ i : Fin m, (n+i+1)^(i+1)`.
* For `m = 0` the nested sum is a sum over the single empty tuple of the empty products, i.e. `1`,
  so the formula reads `T(n+1, 1) = n!`, which is correct.
* All arithmetic is done in `ℚ` (the formula contains divisions). The denominators never vanish
  since `j t ≤ n`. The identity was checked numerically for `n ≤ 6`, `m ≤ 4`.
-/

namespace OMA.S_oeis_a132393

/-- The summand of Kurkov's formula for a tuple `j = (j_1, …, j_m)` (indexed from `0`). -/
def term (n m : ℕ) (j : Fin m → ℕ) : ℚ :=
  (-1 : ℚ) ^ (n * m + ∑ t, j t) *
    (∏ p : Fin m, ∏ q ∈ Finset.univ.filter (fun q : Fin m => q < p),
      (((j q : ℚ) - (j p : ℚ) + ((p : ℕ) : ℚ) - ((q : ℕ) : ℚ)) ^ 2)) *
    ∏ t : Fin m, ((Nat.descFactorial (n + t) (j t) : ℚ) /
      ((((n : ℚ) - (j t : ℚ) + ((t : ℕ) : ℚ) + 1) ^ (m + 1)) *
        ((Nat.factorial (j t + (m - 1 - t)) : ℕ) : ℚ)))

/-- The right-hand side of Kurkov's formula: the sum over `n ≥ j_1 ≥ … ≥ j_m ≥ 0`, times the
prefactor `(n+m)! * Product_{i=1..m} (n+i)^i`. -/
def rhs (n m : ℕ) : ℚ :=
  ((Nat.factorial (n + m) : ℕ) : ℚ) * (∏ i : Fin m, ((n : ℚ) + (i : ℕ) + 1) ^ ((i : ℕ) + 1)) *
    ∑ j ∈ (Fintype.piFinset fun _ : Fin m => Finset.range (n + 1)).filter (fun j => Antitone j),
      term n m j

/-- Kurkov's conjecture: `T(n+m+1, m+1) = rhs n m` for all `n, m ≥ 0`. -/
theorem main : ∀ n m : ℕ, ((Nat.stirlingFirst (n + m + 1) (m + 1) : ℕ) : ℚ) = rhs n m := by
  sorry

end OMA.S_oeis_a132393
