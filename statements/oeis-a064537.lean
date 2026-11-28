import Mathlib

/-!
# A064537: Limit of the recursion B[k] = P[k](B[k-1]), where B_[0] = (1,2,3,4,5,...) and P[k] is the permutation that permutes the entries k+j and 2k + j for all j = 1,..,k.

Source: https://oeis.org/A064537
Credit: @Solfanbtc

Sequences are indexed from position 1. `B_0(i) = i`; `B_k` is `B_{k-1}` with the blocks of
positions `k+1..2k` and `2k+1..3k` exchanged (the entry's Maple program), i.e.
`B_k(i) = B_{k-1}(i + k)` for `k < i ≤ 2k`, `B_k(i) = B_{k-1}(i - k)` for `2k < i ≤ 3k`, and
`B_k(i) = B_{k-1}(i)` otherwise. Step `k` only moves positions `> k`, so position `n` is fixed
from step `n` on and the limit is `a(n) = B_n(n)`. Checked with `#eval`: this gives
1, 3, 5, 7, 4, 6, 12, 14, 16, 11, 2, …, as listed, and `B_60(n) = B_n(n)` for `n ≤ 40`.

Conjecture (from the entry): A064537 is a permutation of the positive integers. `main` states
that `a` is a bijection from `{n ≥ 1}` onto itself.
-/

namespace OMA.S_oeis_a064537

/-- The position permutation `P_k`: exchanges the blocks `k+1..2k` and `2k+1..3k`. -/
def swap (k i : ℕ) : ℕ :=
  if k < i ∧ i ≤ 2 * k then i + k else if 2 * k < i ∧ i ≤ 3 * k then i - k else i

/-- `B k i`: the entry at position `i` of `B_k`. -/
def B : ℕ → ℕ → ℕ
  | 0, i => i
  | k + 1, i => B k (swap (k + 1) i)

/-- A064537(n), the limit of `B_k(n)`. -/
def a (n : ℕ) : ℕ := B n n

/-- A064537 is a permutation of the positive integers. -/
theorem main : Set.BijOn a {n | 1 ≤ n} {n | 1 ≤ n} := by
  sorry

end OMA.S_oeis_a064537
