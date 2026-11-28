import Mathlib

/-!
# A083480: Compress the triangular array A049597 by suppressing zero entries and reversing the order of each row.

Source: https://oeis.org/A083480
Credit: @Solfanbtc

A049597: `T(n, k)` (`0 ≤ k ≤ n`) is the coefficient of `q^(n-k)` in `Σ_{r=0}^{k} [k, r]_q`, the
sum of the Gaussian polynomials (the Maple program of A083480). `T(n, k) = 0` for `k > n`. The
Gaussian polynomials are defined by the `q`-Pascal rule `[k, 0] = 1`, `[0, r+1] = 0`,
`[k+1, r+1] = [k, r] + q^(r+1) [k, r+1]`. A083480 lists row `n` of A049597 with the zero entries
removed, in reverse order. (Python with this definition reproduces the data of A083480 through
row 15.)

Conjecture (Franklin T. Adams-Watters, May 27 2008; in A083480 and, reindexed, in A049597):
"it appears that T(n-1,k-1) is the number of partitions of n with k objects in the first hook;
i.e., with (largest part size) + (number of parts) - 1 = k". In A083480's indexing this is the
statement that the `j`-th entry of row `n` (from `T(1,0)`) counts the partitions of `n` with
`n - (max part) - (number of parts) + 1 = j`. Stated for all `1 ≤ k ≤ n`. (Adams-Watters notes it
implies the comment's informal conjecture on the row lengths, which is not stated separately.)

Remark: the identity seems to follow directly. Removing the first hook (largest part `a`,
`b` parts, `a + b - 1 = k`) leaves a partition of `n - k` inside a `(b-1) × (a-1)` box, and these
are counted by the coefficient of `q^(n-k)` in `[k-1, b-1]_q`. Checked in Python for `n ≤ 21`.
-/

namespace OMA.S_oeis_a083480

open Polynomial

/-- The Gaussian polynomial `[k, r]_q`, by the `q`-Pascal rule. -/
noncomputable def gauss : ℕ → ℕ → ℤ[X]
  | _, 0 => 1
  | 0, _ + 1 => 0
  | k + 1, r + 1 => gauss k r + X ^ (r + 1) * gauss k (r + 1)

/-- A049597 `T(n, k)`. -/
noncomputable def T (n k : ℕ) : ℤ :=
  if k ≤ n then (∑ r ∈ Finset.range (k + 1), gauss k r).coeff (n - k) else 0

/-- The number of partitions of `n` with first hook `(largest part) + (number of parts) - 1 = k`. -/
def hookCount (n k : ℕ) : ℕ :=
  (Finset.univ.filter (fun p : Nat.Partition n => p.parts.sup + p.parts.card - 1 = k)).card

theorem main : ∀ n k : ℕ, 1 ≤ k → k ≤ n → T (n - 1) (k - 1) = hookCount n k := by
  sorry

end OMA.S_oeis_a083480
