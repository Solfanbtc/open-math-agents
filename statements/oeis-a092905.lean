import Mathlib

/-!
# A092905: Triangle, read by rows, such that the partial sums of the n-th row form the n-th diagonal, for n>=0, where each row begins with 1.

Source: https://oeis.org/A092905
Credit: @Solfanbtc

The triangle `T(n, k)`, `0 ≤ k ≤ n`, is given by the entry's formula
`T(n, k) = ∑_{j=0..k} T(n-k, j)` with `T(n, 0) = 1` and `T(n, k) = 0` for `k > n`
(equivalently the PARI program of the entry); this reproduces every term of %S, %T, %U.

Conjecture (Wolfdieter Lang, Dec 03 2012): the triangle with entries `a(n, m) = T(n-1, m-1)`,
`n ≥ 1`, `m = 1, ..., n`, is obtained from the partition array A103921 by summing, in row `n`,
all entries belonging to part number `m`. A103921 lists, for the partitions of `n` with `m`
parts, the number of distinct parts of each, so the conjecture says: summing the number of
distinct parts over all partitions of `n` into exactly `m` parts gives `T(n-1, m-1)`.
Example: the partitions of 6 into 4 parts are 1113 and 1122, with 2 distinct parts each, and
`T(5, 3) = 4`. Checked by computer for all `1 ≤ m ≤ n < 30`.
-/

namespace OMA.S_oeis_a092905

/-- The triangle A092905: `T n 0 = 1`, `T n k = 0` for `k > n`, and
`T n k = ∑_{j=0..k} T (n - k) j` for `1 ≤ k ≤ n`. -/
def T : ℕ → ℕ → ℕ
  | _, 0 => 1
  | n, k + 1 =>
    if h : k + 1 ≤ n then
      ∑ j : Fin (k + 2), T (n - (k + 1)) j
    else 0
termination_by n => n
decreasing_by omega

/-- Lang's conjecture: for `1 ≤ m ≤ n`, the sum over the partitions of `n` into exactly `m` parts
of the number of distinct parts equals `T (n - 1) (m - 1)`. -/
theorem main :
    ∀ n m : ℕ, 1 ≤ m → m ≤ n →
      ∑ p ∈ (Finset.univ : Finset n.Partition).filter (fun p => p.parts.card = m),
        p.parts.toFinset.card = T (n - 1) (m - 1) := by
  sorry

end OMA.S_oeis_a092905
