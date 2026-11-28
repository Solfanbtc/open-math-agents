import Mathlib

/-!
# A288760: nonnegative rationals obtainable in `n` steps of `+, -, ×, ÷` from `{1}`

Source: https://oeis.org/A288760
Credit: @Solfanbtc

`a(n)` is the number of distinct nonnegative rational numbers that can be obtained in `n` steps by
applying addition, subtraction, multiplication and division to any two potentially identical
numbers from the complete set of numbers created in `n - 1` steps, starting with the set `{1}`.
Data: `1, 3, 6, 24, 300, 37761, 451572162` (`n = 0, ..., 6`). The entry says: "The conjectured
value of `a(6) = 451572162` needs independent verification" (value from Markus Sigg, 2017, after
an earlier wrong `a(6)` was removed). We state `a(6) = 451572162`.

Definition, following the entry's examples (`S(1) = {0, 1, 2}`,
`S(2) = {0, 1/2, 1, 2, 3, 4}`, and `S(3)` with 24 elements): `S(0) = {1}` and `S(n+1)` is the set
of all nonnegative `x + y, x - y, x · y` and `x / y` (`y ≠ 0`) for `x, y ∈ S(n)`. Keeping negative
results in the sets instead would not change the absolute values obtained (`|x ± y|`, `|x y|`,
`|x / y|` only depend on `|x|, |y|` up to the choice of sign), so this reading is unambiguous.
A python3 mirror of `S` gives `1, 3, 6, 24, 300` for `n = 0, ..., 4`.
-/

namespace OMA.S_oeis_a288760

/-- All results of `+, -, ×, ÷` (division by nonzero numbers) on pairs from `s`. -/
def ops (s : Finset ℚ) : Finset ℚ :=
  (s ×ˢ s).biUnion fun p =>
    {p.1 + p.2, p.1 - p.2, p.1 * p.2} ∪ (if p.2 = 0 then ∅ else {p.1 / p.2})

/-- `S(n)`: the nonnegative numbers obtained in `n` steps. -/
def S : ℕ → Finset ℚ
  | 0 => {1}
  | n + 1 => (ops (S n)).filter fun q => 0 ≤ q

/-- `A288760(n) = #S(n)`. -/
def a (n : ℕ) : ℕ := (S n).card

/-- The conjectured value `a(6) = 451572162`. -/
theorem main : a 6 = 451572162 := by
  sorry

end OMA.S_oeis_a288760
