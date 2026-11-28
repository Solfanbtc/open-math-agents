import Mathlib

/-!
# A055392: bracketings of 0#0#...#0 giving 0, where # is NOR

Source: https://oeis.org/A055392
Credit: @Solfanbtc

`a(n)` is the number of bracketings of `0 # 0 # ... # 0` (`n` zeros) giving result `0`, where
`0 # 0 = 1` and `0 # 1 = 1 # 0 = 1 # 1 = 0` (NOT OR). Offset 1: 1, 0, 2, 1, 12, 14, 100, ...

Model: a bracketing of `n` operands is a full binary tree with `n` leaves, i.e. a `BinaryTree Unit` with
`n - 1` internal nodes (Mathlib's `BinaryTree.treesOfNumNodesEq (n - 1)` is the finset of all of them);
each leaf is the operand `0` (`false`), each node applies `#`.

Conjecture (R. J. Mathar, Nov 26 2012), for `n ≥ 6` (so that `a(n-5)` is a term, offset 1):
`500 n(n-1) a(n) + 100(n-1)(5n-12) a(n-1) + 20(25n^2-463n+846) a(n-2)
 + (-140161n^2+966559n-1637508) a(n-3) + 2(250n^2-26509n+105084) a(n-4)
 + 98036(4n-19)(4n-21) a(n-5) = 0`.

Sanity check: python (dynamic programming over the root split) reproduces all 27 listed terms and
the recurrence for `6 ≤ n ≤ 400`; `#eval` in Lean gives the first listed terms.
-/

namespace OMA.S_oeis_a055392

/-- Value of a bracketing: leaves are `0` (`false`), nodes compute `x # y = NOT (x OR y)`. -/
def ev : BinaryTree Unit → Bool
  | .nil => false
  | .node _ l r => !(ev l || ev r)

/-- A055392: bracketings of `n` zeros (trees with `n - 1` nodes) giving `0`. -/
def a (n : ℕ) : ℕ := ((BinaryTree.treesOfNumNodesEq (n - 1)).filter (fun t => ev t = false)).card

/-- Mathar's conjectured recurrence. -/
theorem main : ∀ n : ℕ, 6 ≤ n →
    let m : ℤ := n;
    500 * m * (m - 1) * a n + 100 * (m - 1) * (5 * m - 12) * a (n - 1)
      + 20 * (25 * m ^ 2 - 463 * m + 846) * a (n - 2)
      + (-140161 * m ^ 2 + 966559 * m - 1637508) * a (n - 3)
      + 2 * (250 * m ^ 2 - 26509 * m + 105084) * a (n - 4)
      + 98036 * (4 * m - 19) * (4 * m - 21) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a055392
