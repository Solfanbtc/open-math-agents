import Mathlib

/-!
# A078098: eventual values of u(k) = |u(k-1) - u(k-2) - u(k-3)|

Source: https://oeis.org/A078098
Credit: @Solfanbtc

Let `u(1) = u(2) = 1`, `u(3) = 2n + 1`, `u(k) = |u(k-1) - u(k-2) - u(k-3)|`; "then for any `n`
`(u(k), u(k+1)) = (v(n), w(n))` for `k` large enough" (the sequence ends up alternating between two
values), and `a(n) = max(v(n), w(n))` (offset 1): `3, 7, 11, 13, 21, 29, …` (e.g. `n = 2`:
`1, 1, 5, 3, 3, 5, 1, 7, 1, 7, …`, `a(2) = 7`). A simulation reproduces all 56 data terms.

Conjecture (Benoit Cloitre, OEIS formula): `a(n)/n` is bounded. Since `a(n)` is the largest of the
values taken by `u(k)` for all large `k`, this is stated as: there is a constant `C` such that for
every `n ≥ 1`, `u(k) ≤ C n` for all sufficiently large `k`. (Python: `a(n)/n ≤ 12.09` for
`n < 300`.) Below `u n k` is 0-indexed: `u n 0 = u n 1 = 1`, `u n 2 = 2n + 1`.
-/

namespace OMA.S_oeis_a078098

/-- `u(k)` for the starting value `2n + 1` (0-indexed). -/
def u (n : ℕ) : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | 2 => 2 * n + 1
  | k + 3 => |u n (k + 2) - u n (k + 1) - u n k|

/-- Cloitre's conjecture: the eventual values of `u` are `O(n)`. -/
theorem main : ∃ C : ℤ, ∀ n : ℕ, 1 ≤ n → ∀ᶠ k in Filter.atTop, u n k ≤ C * n := by
  sorry

end OMA.S_oeis_a078098
