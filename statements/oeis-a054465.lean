import Mathlib

/-!
# A054465: Numbers k such that Sum_{j=1..k} d(j) is an integer, d(j) = the decimal fraction 0.2j.

Source: https://oeis.org/A054465
Credit: @Solfanbtc

d(j) is the decimal fraction "0." followed by the decimal digits of 2j (e.g. d(14) = 0.28):
d(j) = 2j / 10^(number of digits of 2j), as in the entry's Mathematica program.
Conjecture (in the entry): the number of k > 0 such that a(k) <= n is asymptotic to C*log(n)
for some C > 0, i.e. the number of terms ≤ n is ~ C log n.

Conventions.
* The terms are the m ≥ 1 with Σ_{j=1}^{m} d(j) ∈ ℤ (computed in ℚ); e.g. 0.2+0.4+0.6+0.8 = 2,
  so 4 is a term. `count n` = number of terms ≤ n.
* "~ C log n with C > 0" is stated as: there is C > 0 with count(n) / (C log n) → 1.
-/

namespace OMA.S_oeis_a054465

/-- d(j) = 0.(digits of 2j). -/
def d (j : ℕ) : ℚ := (2 * j : ℚ) / 10 ^ (Nat.digits 10 (2 * j)).length

/-- m is a term: the partial sum up to m is an integer. -/
def IsTerm (m : ℕ) : Prop := 1 ≤ m ∧ ∃ z : ℤ, ∑ j ∈ Finset.Icc 1 m, d j = z

open scoped Classical in
/-- Number of terms ≤ n. -/
noncomputable def count (n : ℕ) : ℕ := ((Finset.Icc 1 n).filter IsTerm).card

theorem main : ∃ C : ℝ, 0 < C ∧
    Filter.Tendsto (fun n : ℕ => (count n : ℝ) / (C * Real.log n)) Filter.atTop (nhds 1) := by
  sorry

end OMA.S_oeis_a054465
