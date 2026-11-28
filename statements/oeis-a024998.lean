import Mathlib

/-!
# A024998: lattice paths s(0..n) with s(0) = 0, |steps 1,2| = 1, |later steps| ≤ 1, s(n) = 1.

Source: https://oeis.org/A024998
Credit: @Solfanbtc

a(n) = number of (s(0), s(1), ..., s(n)) such that every s(i) is an integer, s(0) = 0,
|s(i) - s(i-1)| = 1 for i = 1,2; |s(i) - s(i-1)| <= 1 for i >= 3, s(n) = 1 (offset 1).

Conjecture (R. J. Mathar, Jun 23 2013, in the entry):
(n+1)*a(n) + (-3n+2)*a(n-1) + (-n-7)*a(n-2) + 3(n-4)*a(n-3) = 0.

Conventions.
* A sequence s is determined by its steps d(i) = s(i) - s(i-1) ∈ {-1, 0, 1}, i = 1..n; the
  conditions are d(1), d(2) ≠ 0 (when those steps exist) and Σ d(i) = s(n) = 1. Below the
  steps are `d : Fin n → Fin 3`, step value `d i - 1`, and step i+1 is `d i`. Brute force
  (python3) gives 1, 0, 3, 6, 19, 52, 150, 428, 1232, 3552, matching the data.
* With offset 1 the recurrence involves a(n-3), so it is stated for n ≥ 4 (all indices ≥ 1).
  It holds on all 28 listed terms for n ≥ 4; with a(k) = 0 for k ≤ 0 it would fail at n = 1, 2, 3.
-/

namespace OMA.S_oeis_a024998

/-- The admissible step sequences of length `n`. -/
def steps (n : ℕ) : Finset (Fin n → Fin 3) :=
  Finset.univ.filter fun d =>
    (∀ i : Fin n, i.val < 2 → d i ≠ 1) ∧ ∑ i, (((d i : ℕ) : ℤ) - 1) = 1

/-- A024998. -/
def a (n : ℕ) : ℕ := (steps n).card

theorem main : ∀ n : ℕ, 4 ≤ n →
    ((n : ℤ) + 1) * a n + (-3 * (n : ℤ) + 2) * a (n - 1) + (-(n : ℤ) - 7) * a (n - 2)
      + 3 * ((n : ℤ) - 4) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a024998
