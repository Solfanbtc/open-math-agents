import Mathlib

/-!
# A066743: a(n) is the number of integers of the form (n^2+1)/(k^2+1), where k = 1,2,3,...,n.

Source: https://oeis.org/A066743
Credit: @Solfanbtc

`a(n)` counts the `k` with `1 ≤ k ≤ n` such that `k^2 + 1` divides `n^2 + 1` (offset 1).
This matches all 103 listed terms (%S, %T, %U), checked in Python.

Conjecture (OEIS entry, %F): `(1/n) * Sum_{i=1..n} a(i) = c * log(log(n))` asymptotically with
`1 < c < 2`. We read "asymptotically" as asymptotic equivalence (`~`, i.e.
`Asymptotics.IsEquivalent` as `n → ∞`) for some constant `c` with `1 < c < 2`.
-/

namespace OMA.S_oeis_a066743

open Filter Asymptotics

/-- `a(n)`: the number of `k ∈ {1, …, n}` with `(k^2 + 1) ∣ (n^2 + 1)`. -/
def a (n : ℕ) : ℕ := ((Finset.Icc 1 n).filter (fun k => (k ^ 2 + 1) ∣ (n ^ 2 + 1))).card

/-- There is `c ∈ (1, 2)` with `(1/n) ∑_{i=1}^n a(i) ~ c log log n`. -/
theorem main : ∃ c : ℝ, 1 < c ∧ c < 2 ∧
    IsEquivalent atTop
      (fun n : ℕ => (1 / (n : ℝ)) * ∑ i ∈ Finset.Icc 1 n, (a i : ℝ))
      (fun n : ℕ => c * Real.log (Real.log n)) := by
  sorry

end OMA.S_oeis_a066743
