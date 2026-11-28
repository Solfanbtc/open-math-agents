import Mathlib

/-!
# A073339: first `k` with `b(k) = 0` for `b(1) = n`, `b(k+1) = b(k) - trunc(k/b(k))`.

Source: https://oeis.org/A073339
Credit: @Solfanbtc

For `n ≥ 1`, define `b(1) = n` and `b(k+1) = b(k) - trunc(k / b(k))`, where `trunc` rounds
toward zero (floor for `x ≥ 0`, ceiling for `x < 0`); this is `Int.tdiv`. `a(n)` is the `k` with
`b(k) = 0` (after which `b` is undefined). Here `c n j = b(j+1)`, so `c n 0 = n` and
`c n (j+1) = c n j - Int.tdiv (j+1) (c n j)`; `a(n) = k + 1` for the first `k` with `c n k = 0`.
(Once `c n k = 0`, Lean's `Int.tdiv _ 0 = 0` keeps it at `0`, which does not affect the claim.)

Conjecture (Benoit Cloitre, 2002): `a(n)` is always defined, i.e. for every `n ≥ 1` the sequence
`b` reaches `0`. Checked with python3: these definitions reproduce the b-file
`a(1..1800)` (e.g. `a(1..11) = 2, 5, 5, 69, 69, 12, 69, 69, 69, 29, 69`). The entry's further
question (is `Σ_{k ≤ n} a(k) / (n^2 log n)` bounded?) is a question and is not stated here.
-/

namespace OMA.S_oeis_a073339

/-- `c n j = b(j+1)` for the sequence started at `b(1) = n`. -/
def c (n : ℤ) : ℕ → ℤ
  | 0 => n
  | j + 1 => c n j - Int.tdiv ((j : ℤ) + 1) (c n j)

/-- The conjecture: for every `n ≥ 1`, `b` reaches `0`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, c n k = 0 := by
  sorry

end OMA.S_oeis_a073339
