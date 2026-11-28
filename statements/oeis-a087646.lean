import Mathlib

/-!
# A087646: first term of the first run of exactly n non-perfect-powers.

Source: https://oeis.org/A087646
Credit: @Solfanbtc

Perfect powers (A001597) are the `m = a^b` with `a ≥ 1`, `b ≥ 2` (so `1` is one). A run of
exactly `n` non-perfect-powers is a block `x+1, …, x+n` of non-powers between two consecutive
perfect powers `x` and `x + n + 1`. `a(n)` is the first term `x + 1` of the first such run, or
`0` if there is none. For example `a(3) = 5` (`5, 6, 7` between `4` and `8`) and `a(2) = 2`
(between `1` and `4`). So `a(n) = 0` iff `n + 1` is never the difference of two adjacent
perfect powers (A023057).

Conjecture (entry): the zeros of the data are genuine, i.e. `a(n) = 0` for
`n = 5, 13, 21, 28, 30, 33, 41, 43, 45` (differences `6, 14, 22, 29, 31, 34, 42, 44, 46`, the
terms of A023057 up to 46). Checked with python3 (all perfect powers up to `10^14`): the
definition reproduces the 47 listed terms, and those nine `n` are exactly the `n ≤ 47` without
a run below `10^14`.
-/

namespace OMA.S_oeis_a087646

/-- `m` is a perfect power `a^b` with `a ≥ 1`, `b ≥ 2`. -/
def IsPerfectPower (m : ℕ) : Prop := ∃ a b : ℕ, 1 ≤ a ∧ 2 ≤ b ∧ a ^ b = m

/-- There is a run of exactly `n` non-perfect-powers. -/
def HasRun (n : ℕ) : Prop :=
  ∃ x : ℕ, IsPerfectPower x ∧ IsPerfectPower (x + n + 1) ∧
    ∀ y : ℕ, x < y → y < x + n + 1 → ¬ IsPerfectPower y

/-- The conjecture: there is no run of exactly `n` non-perfect-powers for these `n`. -/
theorem main : ∀ n ∈ ({5, 13, 21, 28, 30, 33, 41, 43, 45} : Finset ℕ), ¬ HasRun n := by
  sorry

end OMA.S_oeis_a087646
