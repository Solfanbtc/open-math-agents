import Mathlib

/-!
# A084700: Smallest k such that k*prime(i)+1 is prime for i = 1 to n.

Source: https://oeis.org/A084700
Credit: @Solfanbtc

Conjecture (Thomas Ordowski, Nov 20 2017, OEIS A084700): log a(n) ~ C n log n.

Translation. a(n) (offset 1) is the least k >= 1 with k * prime(i) + 1 prime for all 1 <= i <= n
(prime(i) = `Nat.nth Nat.Prime (i - 1)`). The conjecture presupposes that a(n) exists for every n
(this is itself open, a prime-tuples statement), so `main` states the existence together with the
asymptotics: for some constant C > 0, log a(n) / (n log n) → C. (C is not specified in the entry.)
The listed terms 1, 2, 2, 6, 6, 6, 6, 192660, ... are those least k.
-/

namespace OMA.S_oeis_a084700

open Filter

/-- `k * prime(i) + 1` is prime for `i = 1..n`. -/
def Good (n k : ℕ) : Prop := ∀ i : ℕ, 1 ≤ i → i ≤ n → (k * Nat.nth Nat.Prime (i - 1) + 1).Prime

/-- a(n): the least `k ≥ 1` that is `Good n k`. -/
noncomputable def a (n : ℕ) : ℕ := sInf {k : ℕ | 1 ≤ k ∧ Good n k}

theorem main :
    (∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 1 ≤ k ∧ Good n k) ∧
    ∃ C : ℝ, 0 < C ∧
      Tendsto (fun n : ℕ => Real.log (a n) / ((n : ℝ) * Real.log n)) atTop (nhds C) := by
  sorry

end OMA.S_oeis_a084700
