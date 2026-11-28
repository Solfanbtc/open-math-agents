import Mathlib

/-!
# A074482: eventual constant step of b(k+1,n) = b(k,n) + (b(k,n) mod (k+n))

Source: https://oeis.org/A074482 (and https://oeis.org/A074483)
Credit: @Solfanbtc

For each `n ≥ 0` consider the recursion `b(1, n) = 1`, `b(k+1, n) = b(k, n) + (b(k, n) mod (k+n))`.
A074482(n) is the number `x` such that `b(k, n) - b(k-1, n) = x` for all `k > y`, where
`y = A074483(n)`: 97, 97, 97, 1, 3, 3, 6, 6, 8, 4, 1, ... (offset 0); in that regime
`b(k, n) = x (k + n + 1)`.

Conjecture (both entries): a(n) is defined for all `n` (as well as A074483), i.e. for every
`n ≥ 0` the differences `b(k, n) - b(k-1, n)` are eventually constant.

Encoding: `c n j = b(j + 1, n)` (so `c n 0 = 1` and `c n (j+1) = c n j + c n j % (j + 1 + n)`);
the sequence is nondecreasing, so the natural-number subtraction is exact.

Sanity check (python): the stabilization reproduces all 45 listed terms of A074482 and the
listed terms of A074483; for `n < 300` it occurs within `2·10^6` steps for every `n` except
`n = 182` (not yet stable there, which does not contradict the conjecture).
-/

namespace OMA.S_oeis_a074482

/-- `c n j = b(j + 1, n)`. -/
def c (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | j + 1 => c n j + c n j % (j + 1 + n)

/-- The conjecture: for every `n`, the differences `b(k, n) - b(k-1, n)` are eventually
constant. -/
theorem main : ∀ n : ℕ, ∃ x Y : ℕ, ∀ j, Y ≤ j → c n (j + 1) - c n j = x := by
  sorry

end OMA.S_oeis_a074482
