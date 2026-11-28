import Mathlib

/-!
# A054393: Number of permutations with certain forbidden subsequences.

Source: https://oeis.org/A054393
Credit: @Solfanbtc

Conjecture (R. J. Mathar, Aug 09 2015, in the entry):
(-n+3) a(n) + (10n-33) a(n-1) + 5(-7n+24) a(n-2) + 2(22n-63) a(n-3) + 2(5n-78) a(n-4)
  + (-55n+357) a(n-5) + (22n-135) a(n-6) + 3(-n+6) a(n-7) = 0.

Conventions.
* The entry does not say which subsequences are forbidden. The only precise definition in the
  entry is its program (J.-F. Alcover, after A054391): a(0) = 1 and, for n ≥ 1, a(n) is the
  (1,1) entry of M^n, where M is the n × n 0/1 matrix with M(i,j) = 1 iff j < i, or i = j ≤ 5,
  or j = i + 1 (1-indexed). This reproduces all 27 listed terms (python3), and is used as the
  definition (0-indexed below: i, j < n, condition j < i ∨ (i = j ∧ i + 1 ≤ 5) ∨ j = i + 1).
* The recurrence involves a(n-7), so it is stated for n ≥ 7; checked for 7 ≤ n < 45.
-/

namespace OMA.S_oeis_a054393

/-- The n × n matrix of the entry's program (0-indexed). -/
def M (n : ℕ) : Matrix (Fin n) (Fin n) ℕ :=
  fun i j => if j.val < i.val ∨ (i = j ∧ i.val + 1 ≤ 5) ∨ j.val = i.val + 1 then 1 else 0

/-- A054393. -/
def a (n : ℕ) : ℕ := if h : 0 < n then (M n ^ n) ⟨0, h⟩ ⟨0, h⟩ else 1

theorem main : ∀ n : ℕ, 7 ≤ n →
    (-(n : ℤ) + 3) * a n + (10 * (n : ℤ) - 33) * a (n - 1) + 5 * (-7 * (n : ℤ) + 24) * a (n - 2)
      + 2 * (22 * (n : ℤ) - 63) * a (n - 3) + 2 * (5 * (n : ℤ) - 78) * a (n - 4)
      + (-55 * (n : ℤ) + 357) * a (n - 5) + (22 * (n : ℤ) - 135) * a (n - 6)
      + 3 * (-(n : ℤ) + 6) * a (n - 7) = 0 := by
  sorry

end OMA.S_oeis_a054393
