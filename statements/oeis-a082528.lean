import Mathlib

/-!
# A082528: Least k such that x(k)=0 where x(1)=n x(k)=k^3*floor(x(k-1)/k^3).

Source: https://oeis.org/A082528
Credit: @Solfanbtc

Conjecture (Benoit Cloitre, OEIS A082528): for real m > 0, define a(n, m) as the least k such that
x(k) = 0, where x(1) = n and x(k) = k^m floor(x(k-1)/k^m); then a(n, m) is asymptotic to
(c(m) n)^(1/(m+1)), where c(m) is a constant depending on m.

Translation: for each real m > 0 there is a constant c > 0 with a(n, m) / (c n)^(1/(m+1)) → 1 as
n → ∞. x is real-valued (k^m is `Real.rpow`), x(1) = n, and a(n, m) is the least k >= 1 with
x(k) = 0 (it exists: once k^m > x(k-1) the floor is 0). A082528 is a(n, 3) (offset 0, a(0) = 1).
Checked numerically: a(n, 3) reproduces the listed terms 1, 2, 2, 2, ...; a(n, m)^(m+1)/n is
about 3.14 for m = 1 (n up to 10^6), and roughly stable for m = 2, 3.
-/

namespace OMA.S_oeis_a082528

open Filter

/-- x(k) for the start `n` and exponent `m` (`x 0 = x 1 = n`). -/
noncomputable def x (n : ℕ) (m : ℝ) : ℕ → ℝ
  | 0 => n
  | 1 => n
  | k + 1 => ((k : ℝ) + 1) ^ m * ⌊x n m k / ((k : ℝ) + 1) ^ m⌋

/-- a(n, m): the least `k ≥ 1` with `x(k) = 0`. -/
noncomputable def a (n : ℕ) (m : ℝ) : ℕ := sInf {k : ℕ | 1 ≤ k ∧ x n m k = 0}

theorem main : ∀ m : ℝ, 0 < m → ∃ c : ℝ, 0 < c ∧
    Tendsto (fun n : ℕ => (a n m : ℝ) / (c * n) ^ (1 / (m + 1))) atTop (nhds 1) := by
  sorry

end OMA.S_oeis_a082528
