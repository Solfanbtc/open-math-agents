import Mathlib

/-!
# A120160: `a(n) = ceiling(Sum_{i=1..n-1} a(i)/4)` for `n ≥ 2`, `a(1) = 1`

Source: https://oeis.org/A120160
Credit: @Solfanbtc

`a(1) = 1`, `a(n) = ⌈(a(1) + ⋯ + a(n-1))/4⌉` (offset 1): `1, 1, 1, 1, 1, 2, 2, 3, 3, 4, 5, 6, …`
(all 54 data terms reproduced).

Base `5/4` (A024634): "in fractional base `a/b`, subtract `a` and carry `b`". The `5/4`-expansion
of `m` is the expansion of `4 ⌊m/5⌋` followed by the digit `m mod 5`, and `m < 5` is a single
digit (so `5 = 40`, `10 = 430`, `36 = 4321031`); hence the number of digits is
`digits m = 1` for `m < 5` and `digits m = digits (4 ⌊m/5⌋) + 1` for `m ≥ 5`.

The entry records three conjectures (Petros Hadjicostas, Jul 2020); all three are stated, as
the parts of `main`:
1. `a(n)` equals the number of multiples of 4 whose representation in base `5/4` has `n - 1`
   digits (`n ≥ 2`). "Multiples of 4" are read as positive multiples: counting `0` (one digit)
   the claim fails at `n = 2` (`0, 4` against `a(2) = 1`); the entry's example (`36, 40, 44` for
   `a(8) = 3`) is consistent with this reading.
2. `a(n)` equals `1/5` times the number of nonnegative integers whose `5/4`-expansion has `n`
   digits (the expansion of `0` having 1 digit), `n ≥ 1`; stated as `5 a(n) = #{…}`.
3. Starting at `a(11) = 5`, the sequence gives all numbers `m` for which, when `m` persons on a
   circle labeled `1..m` are counted from person 1 and every 5th person is removed, the last
   survivor is in `{1, 2, 3, 4}`: `{a(n) : n ≥ 11} = {m ≥ 5 : survivor(m) ≤ 4}` (`m ≤ 4` is
   excluded by "starting at `a(11) = 5`").
Python: 1 and 2 hold for all `n` with `5/4`-expansions of numbers below `400000`, 3 for `m < 3000`.
-/

namespace OMA.S_oeis_a120160

/-- A120160 (`a 0 = 0` is a placeholder outside the offset). -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => ((∑ i : Fin (n + 2), a i) + 3) / 4
decreasing_by exact i.isLt

/-- Number of digits of the base-`5/4` expansion of `m`. -/
def digits (m : ℕ) : ℕ := if m < 5 then 1 else digits (4 * (m / 5)) + 1
decreasing_by omega

/-- Josephus elimination with step 5: `go fuel l i` removes, from position `i`, every 5th
person of the circle `l` until one is left. -/
def go : ℕ → List ℕ → ℕ → ℕ
  | 0, l, _ => l.headD 0
  | f + 1, l, i =>
    if l.length ≤ 1 then l.headD 0 else go f (l.eraseIdx ((i + 4) % l.length)) ((i + 4) % l.length)

/-- The last survivor among persons `1..m`, counting from person 1, removing every 5th. -/
def survivor (m : ℕ) : ℕ := go m (List.range' 1 m) 0

/-- Hadjicostas' three conjectures. -/
theorem main :
    (∀ n : ℕ, 2 ≤ n → a n = {m : ℕ | 0 < m ∧ 4 ∣ m ∧ digits m = n - 1}.ncard) ∧
    (∀ n : ℕ, 1 ≤ n → 5 * a n = {m : ℕ | digits m = n}.ncard) ∧
    ({x | ∃ n, 11 ≤ n ∧ a n = x} = {m : ℕ | 5 ≤ m ∧ survivor m ≤ 4}) := by
  sorry

end OMA.S_oeis_a120160
