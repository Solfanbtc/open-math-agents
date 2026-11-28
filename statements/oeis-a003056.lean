import Mathlib

/-!
# A003056: n appears n+1 times. Also the array A(n,k) = n+k (n >= 0, k >= 0) read by antidiagonals. Also inverse of triangular numbers.

Source: https://oeis.org/A003056
Credit: @Solfanbtc

`A003056(n)` (offset 0) is the largest `m` with `m(m+1)/2 ≤ n`; its generating function is
`(1 - x)⁻¹ ∑_{m ≥ 1} x^{m(m+1)/2}` (entry, %F), i.e. its `n`-th coefficient is
`#{m ≥ 1 : m(m+1)/2 ≤ n}`.

Claim (T. Amdeberhan, Jun 03 2012, in the entry): `A003056(n)` is also the maximum number of 1's
in the list of hook lengths of a partition of `n`; the entry (Jonathan Sondow, Dec 17 2012) says
that Fan, Yang and Yu (2012) prove this conjecture of Amdeberhan on the generating function of
`a(n)`: the generating function of the maximum number of 1-hooks of partitions of `n` is
`(1 - x)⁻¹ ∑_{m ≥ 1} x^{m(m+1)/2}`. (A. R. B. Fan, H. R. L. Yang, R. T. Yu, "On the Maximum
Number of k-Hooks of Partitions of n", arXiv:1212.3505; the paper treats k-hooks in general,
this entry and this statement concern 1-hooks only.)

Status: SOLVED (Fan–Yang–Yu 2012). Stated as: for every `n`, the maximum over partitions of `n`
of the number of cells with hook length 1 equals the `n`-th coefficient of
`(1 - x)⁻¹ ∑_{m ≥ 1} x^{m(m+1)/2}`, namely `#{m : 1 ≤ m ≤ n, m(m+1)/2 ≤ n}`.

Conventions:
* A partition is listed as its parts in decreasing order `l = [l₀ ≥ l₁ ≥ ...]`; its cells are
  `(i, j)` with `i < length l` and `j < lᵢ`; the hook length of `(i, j)` is
  `(lᵢ - j - 1) + #{i' > i : l_{i'} > j} + 1` (arm + leg + 1).
* A python3 check with this definition: the maximum equals the coefficient for `n ≤ 25`
  (e.g. for `n = 4` the counts are `1, 1, 1, 2, 2`, maximum 2, as in the entry's example), and
  the Lean kernel (`decide`) confirms `oneHooks` is `2, 1, 3, 1` on `[2,1,1], [2,2], [3,2,1], [4]`.
-/

namespace OMA.S_oeis_a003056

/-- Hook length of the cell `(i, j)` of the partition with decreasing parts `l`. -/
def hook (l : List ℕ) (i j : ℕ) : ℕ :=
  (l.getD i 0 - j - 1) + ((Finset.Ioo i l.length).filter (fun i' => j < l.getD i' 0)).card + 1

/-- Number of cells of the partition (decreasing parts `l`) whose hook length is 1. -/
def oneHooks (l : List ℕ) : ℕ :=
  ((Finset.range l.length ×ˢ Finset.range (l.headD 0)).filter
    (fun c => c.2 < l.getD c.1 0 ∧ hook l c.1 c.2 = 1)).card

/-- Parts of a partition in decreasing order. -/
def sortedParts {n : ℕ} (p : Nat.Partition n) : List ℕ := p.parts.sort (· ≥ ·)

/-- Amdeberhan's conjecture (proved by Fan, Yang and Yu): the maximum number of 1-hooks of a
partition of `n` is the `n`-th coefficient of `(1 - x)⁻¹ ∑_{m ≥ 1} x^{m(m+1)/2}`. -/
theorem main : ∀ n : ℕ,
    IsGreatest {c | ∃ p : Nat.Partition n, c = oneHooks (sortedParts p)}
      ((Finset.Icc 1 n).filter (fun m => m * (m + 1) / 2 ≤ n)).card := by
  sorry

end OMA.S_oeis_a003056
