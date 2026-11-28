import Mathlib

/-!
# A095811: Greatest number, not divisible by 4, with exactly n partitions into three squares.

Source: https://oeis.org/A095811
Credit: @Solfanbtc

`r(m)` is the number of ways to write `m = a^2 + b^2 + c^2` with `0 ≤ a ≤ b ≤ c` (partitions
into three squares; "a square can be zero"). A095811(n) (`n ≥ 1`) is the greatest `m` with
`4 ∤ m` and `r(m) = n`. (Multiples of 4 are excluded because `r(4m) = r(m)`.)

The entry says: "These are conjectured values. The Mathematica program checks numbers up to
10^6." So the conjecture is that the 30 listed values are correct: for each `n = 1, …, 30`, the
`n`-th listed value is the greatest `m` with `4 ∤ m` and `r(m) = n`. This includes that such a
greatest `m` exists. Checked with python3: up to `2·10^6`, the greatest such `m` for
`n = 1..30` are exactly the listed values.
-/

namespace OMA.S_oeis_a095811

/-- `r(m)`: the number of triples `0 ≤ a ≤ b ≤ c` with `a^2 + b^2 + c^2 = m`. -/
def r (m : ℕ) : ℕ :=
  ((Finset.range (m + 1) ×ˢ Finset.range (m + 1) ×ˢ Finset.range (m + 1)).filter
    (fun t => t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧ t.1 ^ 2 + t.2.1 ^ 2 + t.2.2 ^ 2 = m)).card

/-- The listed values `a(1), …, a(30)`. -/
def vals : List ℕ :=
  [427, 1555, 3763, 6307, 13843, 16003, 21547, 34483, 48427, 54763, 85507, 90787, 111763,
    103387, 166147, 137083, 222643, 211843, 289963, 253507, 296587, 319867, 462883, 375523,
    393187, 546067, 502483, 532123, 615883, 590947]

/-- The conjecture: the listed values are the true values of A095811. -/
theorem main : ∀ i : ℕ, i < 30 →
    IsGreatest {m : ℕ | ¬ 4 ∣ m ∧ r m = i + 1} (vals.getD i 0) := by
  sorry

end OMA.S_oeis_a095811
