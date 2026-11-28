import Mathlib

/-!
# A078345: Numbers k such that F(k) mod k divides F(F(k) mod k)

Source: https://oeis.org/A078345
Credit: @Solfanbtc

Numbers `k ≥ 1` such that `r = F(k) mod k` divides `F(r)` (`F` the Fibonacci numbers), with the
usual convention that `0 ∣ 0` when `r = 0` (`F(0) = 0`; e.g. `k = 1, 5, 12` are terms):
`1, 2, 5, 8, 10, 11, 12, 13, 19, …` (this reproduces all 63 data terms). `a(n)` (offset 1) is the
`n`-th term.

Conjecture (Benoit Cloitre, OEIS formula): `a(n)` is asymptotic to `c n log(n)` with `c > 0.7`.
Stated as: there is `c > 0.7` with `a(n)/(n log n) → c`.
-/

namespace OMA.S_oeis_a078345

/-- `k` is a term of A078345. -/
def IsTerm (k : ℕ) : Prop := 1 ≤ k ∧ Nat.fib k % k ∣ Nat.fib (Nat.fib k % k)

/-- A078345 (offset 1): the `n`-th term. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsTerm (n - 1)

/-- Cloitre's conjecture: `a(n) ~ c n log n` for some `c > 0.7`. -/
theorem main : ∃ c : ℝ, 0.7 < c ∧
    Filter.Tendsto (fun n : ℕ => (a n : ℝ) / (n * Real.log n)) Filter.atTop (nhds c) := by
  sorry

end OMA.S_oeis_a078345
