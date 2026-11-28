import Mathlib

/-!
# A101591: where the k-Somos sequences first become nonintegral

Source: https://oeis.org/A101591 (with https://oeis.org/A030127)
The `k`-Somos sequence is `S(0) = ... = S(k-1) = 1` and, for `n ≥ k`,
`S(n) = (∑_{j=1}^{⌊k/2⌋} S(n-j) S(n-k+j)) / S(n-k)` (example section of the entry).
A030127(k) (offset 8) is the index at which the `k`-Somos sequence first becomes nonintegral
(17, 19, 20, 22, 24, 27, ...), and A101591 lists the `k ≥ 8` for which this index is odd.
The entry's conjecture: "When k is in this sequence, the k-Somos sequence first becomes
nonintegral at 2*k + 1; otherwise, the k-Somos sequence first becomes nonintegral at 2*k."

We state: for every `k ≥ 8`, the `k`-Somos sequence has a first nonintegral term, at an index
`N` with `N = 2k` or `N = 2k + 1` (`k` is in A101591 exactly when `N` is odd, i.e. `N = 2k + 1`,
and otherwise `N = 2k`). This includes that the first nonintegral term exists for every
`k ≥ 8`, which the conjecture presupposes (A030127: "There does not seem to be a published proof
that a(n) is defined for all n>=8").

Conventions. Terms are rationals; the division is by `S(n-k)`, which is positive. `somos k n`
is the list `S(0), ..., S(n-1)`.
Checked with python3 (exact fractions): the first nonintegral index reproduces all 62 listed
terms of A030127 (`k = 8..69`), and lies in `{2k, 2k+1}` for all `8 ≤ k < 200`.

Credit: @Solfanbtc
-/

namespace OMA.S_oeis_a101591

/-- The list `[S(0), ..., S(n-1)]` of the `k`-Somos sequence. -/
def somos (k : ℕ) : ℕ → List ℚ
  | 0 => []
  | n + 1 =>
    let l := somos k n
    l ++ [if n < k then 1 else
      (∑ j ∈ Finset.Icc 1 (k / 2), l.getD (n - j) 0 * l.getD (n - k + j) 0) / l.getD (n - k) 0]

/-- The `n`-th term `S(n)` of the `k`-Somos sequence. -/
def S (k n : ℕ) : ℚ := (somos k (n + 1)).getD n 0

/-- `q` is an integer. -/
def IsIntegral (q : ℚ) : Prop := ∃ z : ℤ, (z : ℚ) = q

theorem main : ∀ k : ℕ, 8 ≤ k →
    ∃ N : ℕ, ¬ IsIntegral (S k N) ∧ (∀ m < N, IsIntegral (S k m)) ∧
      (N = 2 * k ∨ N = 2 * k + 1) := by
  sorry

end OMA.S_oeis_a101591
