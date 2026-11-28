import Mathlib

/-!
# A074980: Numbers which are not of the form m^p - n^q where p = 2 or 3, q = 2 or 3.

Source: https://oeis.org/A074980
Credit: @Solfanbtc

Conjecture (OEIS A074980): "This is a famous hard problem and the terms shown are only
conjectured values" (checked for squares and cubes through 1.134 * 10^25). `main`: for
1 <= n <= 378 (the listed range), n is not of the form m^p - k^q with p, q ∈ {2, 3} iff n is one
of the 55 listed terms. The "if" direction is the conjecture; the "only if" direction is witnessed
by explicit representations (e.g. 146 = 195^3 - 2723^2).

Conventions: m and k are positive integers (as in the companion entry A074981). Allowing 0 would
also make every square and cube representable; numerically both readings give the same list up
to 378 (searching squares below 4 * 10^10 and cubes below 2.2 * 10^11).
-/

namespace OMA.S_oeis_a074980

/-- `n = m^p - k^q` with `m, k ≥ 1` and `p, q ∈ {2, 3}`. -/
def IsRep (n : ℕ) : Prop :=
  ∃ m k p q : ℕ, 0 < m ∧ 0 < k ∧ (p = 2 ∨ p = 3) ∧ (q = 2 ∨ q = 3) ∧
    (n : ℤ) = (m : ℤ) ^ p - (k : ℤ) ^ q

/-- The listed terms. -/
def terms : Finset ℕ :=
  {6, 10, 14, 34, 42, 46, 50, 58, 62, 66, 70, 78, 82, 86, 90, 102, 110, 114, 122, 130, 134, 158,
   162, 166, 178, 182, 194, 202, 206, 210, 214, 226, 230, 234, 238, 246, 250, 254, 258, 266, 274,
   278, 290, 302, 306, 310, 314, 322, 326, 330, 338, 354, 358, 374, 378}

theorem main : ∀ n : ℕ, 1 ≤ n → n ≤ 378 → (¬ IsRep n ↔ n ∈ terms) := by
  sorry

end OMA.S_oeis_a074980
