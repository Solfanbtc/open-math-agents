import Mathlib

/-!
# A073369: Let c(1)=n, e=2.71... and c(k+1)=floor(c(k)/e) if c(k) is even, c(k+1)=floor(e*c(k)) otherwise; sequence gives the smallest value a(n) such that c(a(n))=0.

Source: https://oeis.org/A073369
Credit: @Solfanbtc

`step c = ⌊c / e⌋` for even `c` and `⌊e c⌋` for odd `c`, and `c(k) = step^[k-1] n`. So `a(n)`,
the least `k ≥ 1` with `c(k) = 0`, is `1 + min {j | step^[j] n = 0}`. For example `n = 1`:
1 → 2 → 0, so `a(1) = 3`. Checked with python3: this reproduces the data 3, 2, 4, 4, 12, 3, 9, ...

Conjecture (B. Cloitre): the sequence always exists (for every `n ≥ 1` the trajectory reaches 0),
and there is a constant `C = 2.9…` such that `∑_{k=1}^{n} a(k) ~ C n log n`.
`main` states both parts, reading "`C = 2.9…`" as `2.9 ≤ C < 3`. (python3: every `n ≤ 3·10^5`
reaches 0; `∑ a(k) / (n log n)` is about 2.84, 2.82, 2.87 at `n = 10^3, 10^4, 10^5`.)
The entry's further question (whether the constant is the same for the analogous sequence with
`π` in place of `e`) has no conjectured answer and is not part of `main`.
-/

namespace OMA.S_oeis_a073369

open Filter Asymptotics Real

/-- One step of the map: `⌊c / e⌋` if `c` is even, `⌊e c⌋` if `c` is odd. -/
noncomputable def step (c : ℕ) : ℕ :=
  if Even c then ⌊(c : ℝ) / exp 1⌋₊ else ⌊exp 1 * (c : ℝ)⌋₊

/-- `a n`: the least `k ≥ 1` with `c(k) = step^[k-1] n = 0`. -/
noncomputable def a (n : ℕ) : ℕ := sInf {j : ℕ | step^[j] n = 0} + 1

theorem main :
    (∀ n : ℕ, 1 ≤ n → ∃ j : ℕ, step^[j] n = 0) ∧
      ∃ C : ℝ, 2.9 ≤ C ∧ C < 3 ∧
        (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n, (a k : ℝ))) ~[atTop] fun n => C * n * log n := by
  sorry

end OMA.S_oeis_a073369
