import Mathlib

/-!
# A081885: Number of steps needed to reach an integer starting with n+1/16 and iterating the map x-->x*ceiling(x).

Source: https://oeis.org/A081885
Credit: @Solfanbtc

Conjecture (Benoit Cloitre, OEIS A081885): let b(n, m) denote the number of steps needed to reach an
integer starting with n + 1/2^m and iterating the map x ↦ x ceiling(x); then Σ_{k=1..n} b(k, m) is
asymptotic to (m+1) n. (A081885 itself is b(n, 4).)

Translation. The conjecture presupposes that b(n, m) is defined, i.e. that the orbit of n + 1/2^m
reaches an integer; `main` states this together with the asymptotics, for every m >= 1 (the
entry's m with denominator 2^m) and every n >= 1 (offset 1). b(n, m) is the least such number of
steps (`sInf`). Asymptotic: (Σ_{k=1..n} b(k, m)) / ((m+1) n) → 1.
Checked numerically: b(n, 4) reproduces the listed terms 8, 5, 3, 8, 18, ...; for n = 3000 the
ratio is 0.999, 0.998, 1.003, 1.007 for m = 1, 2, 3, 4.
-/

namespace OMA.S_oeis_a081885

open Filter

/-- The map x ↦ x ⌈x⌉ on ℚ. -/
def f (x : ℚ) : ℚ := x * ⌈x⌉

/-- b(n, m): the least number of steps from n + 1/2^m to an integer. -/
noncomputable def b (n m : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ z : ℤ, f^[k] ((n : ℚ) + 1 / 2 ^ m) = z}

theorem main : ∀ m : ℕ, 1 ≤ m →
    (∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, ∃ z : ℤ, f^[k] ((n : ℚ) + 1 / 2 ^ m) = z) ∧
    Tendsto (fun n : ℕ => ((∑ k ∈ Finset.Icc 1 n, b k m : ℕ) : ℝ) / (((m : ℝ) + 1) * n)) atTop
      (nhds 1) := by
  sorry

end OMA.S_oeis_a081885
