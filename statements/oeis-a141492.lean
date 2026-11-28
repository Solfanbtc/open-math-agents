import Mathlib

/-!
# A141492: a(n) is the floor of the reciprocal of the difference between the 10^n-th root of 10^n and 1.

Source: https://oeis.org/A141492 (Cino Hilliard, 2008; name corrected and comment by
Jon E. Schoenfield, Aug 05 2021; OEIS Foundation, CC BY-SA 4.0).
Credit: @Solfanbtc

a(n) = floor(1/((10^n)^(1/10^n) - 1)), n ≥ 1.

The entry contains two conjectures, both stated here (as a conjunction):
1. (Cino Hilliard) "This sequence converges to the number of primes < 10^n or Pi(10^n)."
2. (Jon E. Schoenfield) a(n) = floor(10^n/(log(10)*n) - 1/2) for n >= 1.

Formalization notes.
* Conjecture 1 cannot mean a(n) - π(10^n) → 0: already a(1) = 3 ≠ 4 = π(10) and the
  difference grows (a(n) ≈ 10^n/(n log 10) while π(10^n) - 10^n/(n log 10) → ∞). It is read in
  the standard asymptotic sense a(n) ~ π(10^n), i.e. a(n)/π(10^n) → 1. In that reading it
  follows from the prime number theorem together with Schoenfield's expansion
  f(x) = 1/(x^(1/x) - 1) = x/log x - 1/2 + O(log x / x).
* `Real.log` is the natural logarithm, `Nat.primeCounting` is π (primes ≤ 10^n; 10^n is not
  prime for n ≥ 1, so this equals the number of primes < 10^n), and x^(1/x) is the real power
  `Real.rpow`.
* A python computation with 200-digit decimals reproduces the 21 listed terms and confirms
  conjecture 2 for 1 ≤ n ≤ 60.
-/

namespace OMA.S_oeis_a141492

open Filter Topology

/-- a(n) = floor(1/((10^n)^(1/10^n) - 1)). -/
noncomputable def a (n : ℕ) : ℤ :=
  ⌊1 / (((10 : ℝ) ^ n) ^ (1 / (10 : ℝ) ^ n) - 1)⌋

theorem main :
    Tendsto (fun n : ℕ => (a n : ℝ) / (Nat.primeCounting (10 ^ n) : ℝ)) atTop (𝓝 1) ∧
    ∀ n : ℕ, 1 ≤ n → a n = ⌊(10 : ℝ) ^ n / (Real.log 10 * n) - 1 / 2⌋ := by
  sorry

end OMA.S_oeis_a141492
