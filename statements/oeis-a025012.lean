import Mathlib

/-!
# A025012: Mathar's recurrence for the central heptanomial coefficients

Source: https://oeis.org/A025012
Credit: @Solfanbtc

A025012 (offset 0): `a(n)` is the largest coefficient of `(1 + x + … + x^6)^n`
(data 1, 1, 7, 37, 231, 1451, 9331, …).

Conjecture (R. J. Mathar, Feb 21 2010, stated in the entry as "D-finite with recurrence"; T. D.
Noe: "I checked that Mathar's conjectured formula fits the 200 terms of the b-file"):
`3n(3n-1)(3n-2) a(n) + (41n^3 - 723n^2 + 1132n - 456) a(n-1)
 + 7(-383n^3 + 2607n^2 - 5992n + 4608) a(n-2) + 49(-83n^3 + 1317n^2 - 6706n + 10512) a(n-3)
 + 343(199n^3 - 2487n^2 + 10394n - 14496) a(n-4) + 2401(n-4)(43n^2 - 437n + 1116) a(n-5)
 - 16807(n-4)(n-5)(5n-24) a(n-6) - 117649(n-5)(n-6)(n-4) a(n-7) = 0`.
`main` states it for `n ≥ 7` (so that every index is at least the offset 0).

Status: D. Zeilberger (Apr 12 2011, in the entry) remarks that such a recurrence can be proved
automatically by the Almkvist-Zeilberger algorithm, which finds a 4th-order recurrence; the
7th-order one above is not proved in the entry. Checked with python3 (exact integers) for
`7 ≤ n < 130`.

Definition. `a(n)` is the maximum of the coefficients of `(1 + X + … + X^6)^n ∈ ℤ[X]`, which has
degree `6n`; we take the maximum over the indices `0, …, 6n`.
-/

namespace OMA.S_oeis_a025012

open Polynomial

/-- A025012: the largest coefficient of `(1 + x + … + x^6)^n`. -/
noncomputable def a (n : ℕ) : ℤ :=
  (Finset.range (6 * n + 1)).sup' ⟨0, by simp⟩
    (fun i => ((∑ j ∈ Finset.range 7, (X : ℤ[X]) ^ j) ^ n).coeff i)

/-- Mathar's 7th-order recurrence for A025012. -/
theorem main : ∀ n : ℕ, 7 ≤ n →
    3 * (n : ℤ) * (3 * n - 1) * (3 * n - 2) * a n
      + (41 * (n : ℤ) ^ 3 - 723 * n ^ 2 + 1132 * n - 456) * a (n - 1)
      + 7 * (-383 * (n : ℤ) ^ 3 + 2607 * n ^ 2 - 5992 * n + 4608) * a (n - 2)
      + 49 * (-83 * (n : ℤ) ^ 3 + 1317 * n ^ 2 - 6706 * n + 10512) * a (n - 3)
      + 343 * (199 * (n : ℤ) ^ 3 - 2487 * n ^ 2 + 10394 * n - 14496) * a (n - 4)
      + 2401 * ((n : ℤ) - 4) * (43 * n ^ 2 - 437 * n + 1116) * a (n - 5)
      - 16807 * ((n : ℤ) - 4) * (n - 5) * (5 * n - 24) * a (n - 6)
      - 117649 * ((n : ℤ) - 5) * (n - 6) * (n - 4) * a (n - 7) = 0 := by
  sorry

end OMA.S_oeis_a025012
