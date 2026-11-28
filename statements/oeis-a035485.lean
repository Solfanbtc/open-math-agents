import Mathlib

/-!
# A035485: Card on top of deck at n-th stage of R. K. Guy's shuffling problem.

Source: https://oeis.org/A035485
Credit: @Solfanbtc

The deck starts as `1, 2, 3, 4, ...` (infinite). At the `n`-th step (`n ≥ 1`), pick up the top
`n` cards and interlace them with the next `n`: the new deck begins
`c_{n+1}, c_1, c_{n+2}, c_2, ..., c_{2n}, c_n` and continues unchanged from position `2n + 1`.
`A035485(n)` is the card on top of the deck after step `n` (with `a(0) = 1`).

The OEIS conjecture: *eventually every number appears on top of the deck*, i.e. every positive
integer `k` equals `A035485(n)` for some `n`.

We model a deck as a function from 0-based positions to cards: `deck n i` is the card at position
`i` after `n` steps. The step `n + 1` (picking up `n + 1` cards) sends position `2i` to old position
`n + 1 + i` and position `2i + 1` to old position `i`, for `i < n + 1`; positions `≥ 2(n + 1)` are
unchanged. A line-by-line python3 mirror of `deck` reproduces all 84 OEIS data terms
(`1, 2, 3, 1, 6, 5, 9, 1, 4, 2, 16, ...`).
-/

namespace OMA.S_oeis_a035485

/-- The deck after `n` steps: `deck n i` is the card at 0-based position `i`. -/
def deck : ℕ → ℕ → ℕ
  | 0, i => i + 1
  | n + 1, i =>
    if i < 2 * (n + 1) then
      (if i % 2 = 0 then deck n (n + 1 + i / 2) else deck n (i / 2))
    else deck n i

/-- `A035485(n)`: the card on top of the deck after step `n`. -/
def a (n : ℕ) : ℕ := deck n 0

-- #eval (List.range 20).map a
-- [1, 2, 3, 1, 6, 5, 9, 1, 4, 2, 16, 10, 12, 14, 23, 16, 18, 20, 17, 27]

/-- Every positive integer eventually appears on top of the deck. -/
theorem main : ∀ k : ℕ, 0 < k → ∃ n, a n = k := by
  sorry

end OMA.S_oeis_a035485
