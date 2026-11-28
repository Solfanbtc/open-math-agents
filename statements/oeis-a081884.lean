import Mathlib

/-!
# A081884: steps to reach an integer from n + 1/8 under x ↦ x * ceiling(x).

Source: https://oeis.org/A081884
Credit: @Solfanbtc

`b(n, m)` is the number of steps needed to reach an integer when starting from `n + 1/2^m` and
iterating `f(x) = x * ⌈x⌉` on `ℚ`; A081884(n) = `b(n, 3)`. Here `b n m` is the least `k` with
`f^[k] (n + 1/2^m)` an integer (`den = 1`).

Conjecture (entry): for every `m` (`m ≥ 1`; for `m = 0` the start is already an integer),
`Σ_{k=1}^n b(k, m)` is asymptotic to `(m + 1) n`. (For `m = 3` this is the entry's remark that
`Σ a(k) ~ 4n`.) The asymptotic presupposes that `b(k, m)` is defined, i.e. that an integer is
always reached, so `main` states this together with `(Σ_{k=1}^n b(k, m)) / n → m + 1`.
Checked with python3: `b(n, 3)` reproduces the 103 listed terms, and for `n = 3000` the averages
`(Σ_{k ≤ n} b(k, m)) / n` are `2.00, 2.99, 4.01, 5.04, 6.03` for `m = 1..5`.
-/

namespace OMA.S_oeis_a081884

open Filter Topology

/-- The map `x ↦ x * ⌈x⌉`. -/
def f (x : ℚ) : ℚ := x * ⌈x⌉

/-- `b(n, m)`: the number of steps to reach an integer from `n + 1/2^m`. -/
noncomputable def b (n m : ℕ) : ℕ :=
  sInf {k : ℕ | (f^[k] ((n : ℚ) + 1 / 2 ^ m)).den = 1}

/-- The conjecture: an integer is always reached, and `Σ_{k=1}^n b(k, m) ~ (m + 1) n`. -/
theorem main : ∀ m : ℕ, 1 ≤ m →
    (∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, (f^[k] ((n : ℚ) + 1 / 2 ^ m)).den = 1) ∧
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, (b n m : ℝ)) / N) atTop
      (𝓝 ((m : ℝ) + 1)) := by
  sorry

end OMA.S_oeis_a081884
