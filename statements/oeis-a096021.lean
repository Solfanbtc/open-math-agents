import Mathlib

/-!
# A096021: Greatest number, not divisible by 4, with exactly n partitions into three distinct
positive squares.

Source: https://oeis.org/A096021
Credit: @Solfanbtc

`r(m)` is the number of ways to write `m = a^2 + b^2 + c^2` with `0 < a < b < c` (partitions
into three distinct positive squares). A096021(n) (`n ≥ 1`) is the greatest `m` with `4 ∤ m`
and `r(m) = n`. (Multiples of 4 are excluded because `r(4m) ≥ r(m)`.)

The entry says: "These are conjectured values. The Mathematica program checks numbers up to
10^6." So the conjecture is that the 30 listed values are correct: for each `n = 1, …, 30`, the
`n`-th listed value is the greatest `m` with `4 ∤ m` and `r(m) = n`. This includes that such a
greatest `m` exists, i.e. the set is nonempty and bounded. Checked with python3: up to
`2·10^6`, the greatest such `m` for `n = 1..30` are exactly the listed values.
-/

namespace OMA.S_oeis_a096021

/-- `r(m)`: the number of triples `0 < a < b < c` with `a^2 + b^2 + c^2 = m`. -/
def r (m : ℕ) : ℕ :=
  ((Finset.range (m + 1) ×ˢ Finset.range (m + 1) ×ˢ Finset.range (m + 1)).filter
    (fun t => 0 < t.1 ∧ t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ t.1 ^ 2 + t.2.1 ^ 2 + t.2.2 ^ 2 = m)).card

/-- The listed values `a(1), …, a(30)`. -/
def vals : List ℕ :=
  [1507, 4323, 5947, 10707, 19723, 30067, 34483, 47107, 58843, 77683, 111763, 106723, 126043,
    166147, 164803, 222643, 217627, 232243, 289963, 319243, 300787, 319867, 462883, 393187,
    546067, 532123, 502483, 615883, 662803, 606643]

/-- The conjecture: the listed values are the true values of A096021. -/
theorem main : ∀ i : ℕ, i < 30 →
    IsGreatest {m : ℕ | ¬ 4 ∣ m ∧ r m = i + 1} (vals.getD i 0) := by
  sorry

end OMA.S_oeis_a096021
