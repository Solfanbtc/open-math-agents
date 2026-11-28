import Mathlib

/-!
# A072491: Define f(1) = 0. For n>=2, let f(n) = n - p where p is the largest prime <= n. a(n) = number of iterations of f to reach 0, starting from n.

Source: https://oeis.org/A072491
Credit: @Solfanbtc

Claim (OEIS entry, %F, Charles R Greathouse IV, 2013): on Cramér's conjecture, `a(n) = O(log* n)`.
This is a conditional statement: Cramér's conjecture implies `a(n) = O(log* n)`.

Conventions:
* `f(0) = f(1) = 0` and `f(n) = n - p` for `n ≥ 2`, `p` the largest prime `≤ n`
  (`Nat.findGreatest Nat.Prime n`). `a(n)` is the least `k` with `f^[k] n = 0` (offset 0, so
  `a(0) = 0`, as in the entry). Checked in Python: this reproduces all 106 listed terms.
* Cramér's conjecture is taken in the form used in formal-conjectures
  (`CramerConjecture.cramer_conjecture`): `p_{n+1} - p_n = O((log p_n)^2)`, with `p_n`
  `= Nat.nth Nat.Prime n` (so `p_0 = 2`).
* `log* x` is the iterated logarithm (natural log): the least `k` with `log^[k] x ≤ 1`. (Changing
  the base of the logarithm changes `log*` by a bounded amount for large `x`; since `log* n`
  tends to infinity, this does not affect the `O`-claim.)
* `O` is `Asymptotics.IsBigO` along `atTop`.
-/

namespace OMA.S_oeis_a072491

open Filter Asymptotics

/-- `f(n) = n - p` with `p` the largest prime `≤ n` for `n ≥ 2`; `f(0) = f(1) = 0`. -/
def f (n : ℕ) : ℕ := if n < 2 then 0 else n - Nat.findGreatest Nat.Prime n

/-- `a(n)`: the number of iterations of `f` needed to reach `0` from `n`. -/
noncomputable def a (n : ℕ) : ℕ := sInf {k : ℕ | f^[k] n = 0}

/-- The iterated logarithm `log* x`: the least `k` with `log^[k] x ≤ 1`. -/
noncomputable def logStar (x : ℝ) : ℕ := sInf {k : ℕ | Real.log^[k] x ≤ 1}

/-- Cramér's conjecture: `p_{n+1} - p_n = O((log p_n)^2)`. -/
def CramerConjecture : Prop :=
  (fun n : ℕ => ((Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n : ℕ) : ℝ)) =O[atTop]
    (fun n : ℕ => (Real.log (Nat.nth Nat.Prime n)) ^ 2)

/-- Greathouse: on Cramér's conjecture, `a(n) = O(log* n)`. -/
theorem main : CramerConjecture →
    (fun n : ℕ => (a n : ℝ)) =O[atTop] (fun n : ℕ => (logStar n : ℝ)) := by
  sorry

end OMA.S_oeis_a072491
