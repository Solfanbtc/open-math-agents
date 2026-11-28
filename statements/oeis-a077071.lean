import Mathlib

/-!
# A077071: Row sums of A077070

Source: https://oeis.org/A077071
Credit: @Solfanbtc

A077070 is the triangle `T(n, k)` (`0 ≤ k ≤ n`) of the powers of 2 in the denominators of the
coefficients of the Legendre polynomials; by the OEIS formula (Kevin Ryde)
`T(n, k) = 2n - wt(n-k) - wt(k)`, `wt` the binary weight, which is used as the definition here.
A077071 (offset 0): `a(n) = ∑_{k=0}^{n} T(n, k)`: `0, 2, 8, 16, 30, 46, 66, …` (all 20 data terms
agree).

Conjecture (Mikhail Kurkov, OEIS comment): given `n` balls, all of which are initially in the
first of `n` numbered boxes, `a(n-1)` is the number of steps of the following process required to
move them all to the last box. A step consists of first identifying `j`, the lowest numbered box
which has at least one ball. If it has only one ball then move it to box `j+1`; otherwise move
half its balls rounded down to box `j+1` and (unless it's the first box) half its balls rounded
down to box `j-1`.

Formalization: a configuration is `c : ℕ → ℕ` (`c i` = balls in box `i`, boxes `1, …, n`); `step`
performs one step; the number of steps required is the least `t` with `step^[t]` of the initial
configuration equal to the final one (all `n` balls in box `n`). Stated for `n ≥ 1`. (A Python
simulation gives `0, 2, 8, 16, 30, 46, 66` for `n = 1..7` and agrees with `a(n-1)` for
`n < 70`; the process never moves a ball past box `n`, since it stops as soon as the lowest
nonempty box is box `n`.)
-/

namespace OMA.S_oeis_a077071

/-- Binary weight. -/
def wt (x : ℕ) : ℕ := (Nat.digits 2 x).count 1

/-- A077071: `a(n) = ∑_{k=0}^{n} (2n - wt(n-k) - wt(k))`. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), (2 * n - wt (n - k) - wt k)

/-- One step of the process on the configuration `c`. -/
noncomputable def step (c : ℕ → ℕ) : ℕ → ℕ :=
  let j := sInf {i | c i ≠ 0}
  let b := c j
  if b = 1 then Function.update (Function.update c j 0) (j + 1) (c (j + 1) + 1)
  else if j = 1 then
    Function.update (Function.update c j (b - b / 2)) (j + 1) (c (j + 1) + b / 2)
  else
    Function.update (Function.update (Function.update c j (b - 2 * (b / 2)))
      (j + 1) (c (j + 1) + b / 2)) (j - 1) (c (j - 1) + b / 2)

/-- Initial configuration: `n` balls in box `1`. -/
def init (n : ℕ) : ℕ → ℕ := fun i => if i = 1 then n else 0

/-- Final configuration: `n` balls in box `n`. -/
def final (n : ℕ) : ℕ → ℕ := fun i => if i = n then n else 0

/-- The number of steps required to move all balls to the last box. -/
noncomputable def steps (n : ℕ) : ℕ := sInf {t : ℕ | step^[t] (init n) = final n}

/-- Kurkov's conjecture: the process takes `a(n-1)` steps. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    (∃ t, step^[t] (init n) = final n) ∧ steps n = a (n - 1) := by
  sorry

end OMA.S_oeis_a077071
