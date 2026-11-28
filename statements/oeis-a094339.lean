import Mathlib

/-!
# A094339: Beginning with 2, least number not occurring earlier that divides the sum of all previous terms.

Source: https://oeis.org/A094339
Credit: @Solfanbtc

`a(1) = 2`, and for `n ≥ 2`, `a(n)` is the least positive integer not among
`a(1), …, a(n-1)` that divides `S = a(1) + ⋯ + a(n-1)`.

Conjecture (OEIS entry): this is a rearrangement of the natural numbers (positive integers):
`n ↦ a(n)` is a bijection from `{n ≥ 1}` onto `{m ≥ 1}`.

Formalization: `terms n` is the list `[a(1), …, a(n)]`. The search for `a(n)` runs over
`1 ≤ d ≤ S`, which always suffices: for `n = 2`, `S = 2` and `d = 1` works; for `n ≥ 3`, `S` is a
sum of at least two distinct positive terms, hence larger than each of them, so `d = S` is an
unused divisor. The fallback value `0` is therefore never used.
Checked with `#eval`: the first 67 values agree with the OEIS data (%S, %T, %U).
-/

namespace OMA.S_oeis_a094339

/-- `terms n = [a(1), …, a(n)]`. -/
def terms : ℕ → List ℕ
  | 0 => []
  | 1 => [2]
  | n + 2 =>
    let l := terms (n + 1)
    let S := l.sum
    l ++ [(((List.range S).map (· + 1)).find?
      (fun d => decide (S % d = 0) && !(l.contains d))).getD 0]

/-- A094339 (offset 1). -/
def a (n : ℕ) : ℕ := (terms n).getD (n - 1) 0

/-- The sequence is a rearrangement of the positive integers. -/
theorem main :
    (∀ i j : ℕ, 1 ≤ i → 1 ≤ j → a i = a j → i = j) ∧
    (∀ m : ℕ, 1 ≤ m → ∃ n : ℕ, 1 ≤ n ∧ a n = m) := by
  sorry

end OMA.S_oeis_a094339
