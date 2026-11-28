import Mathlib

/-!
# A070916: a(1)=1, a(n) is the smallest integer >= a(n-1) such that a(n)*a(n-1) - 1 is prime.

Source: https://oeis.org/A070916
Credit: @Solfanbtc

Conjecture (in the entry): lim_{n -> infinity} a(n)/(n*log(n)) = C = 1.075... .

Conventions.
* `a 0` here is the entry's a(1) = 1 (index shifted by one); a(n+1) is the least m ≥ a(n) with
  m·a(n) - 1 prime (it exists by Dirichlet's theorem, since gcd(a(n), 1) = 1; `sInf`).
  Data: 1, 3, 4, 5, 6, 7, 12, 14, 16, ...
* With the entry's indexing n ↦ a(n) = `a (n - 1)`. A constant given by its leading digits
  ("1.075...") is stated as: the limit exists and lies in [1.075, 1.076).
  (python3: a(n)/(n log n) = 1.0010 at n = 1000, 1.0753 at n = 10^4.)
-/

namespace OMA.S_oeis_a070916

/-- A070916 with index shifted by one. -/
noncomputable def a : ℕ → ℕ
  | 0 => 1
  | n + 1 => sInf {m : ℕ | a n ≤ m ∧ (m * a n - 1).Prime}

theorem main : ∃ C : ℝ,
    Filter.Tendsto (fun n : ℕ => (a (n - 1) : ℝ) / (n * Real.log n)) Filter.atTop (nhds C) ∧
      1.075 ≤ C ∧ C < 1.076 := by
  sorry

end OMA.S_oeis_a070916
