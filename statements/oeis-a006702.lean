import Mathlib

/-!
# A006702: Solution to a Pellian equation: least x such that x^2 - n*y^2 = +- 1.

Source: https://oeis.org/A006702 (see also https://oeis.org/A003285)
Credit: @Solfanbtc

The source's claim (Ralf Stephan, Dec 12 2013; with the conjecture of A003285 on m):
the denominators b(j) of the continued fraction convergents to sqrt(n) satisfy the linear
recurrence b(j+2m) = C*b(j+m) - (-1)^m * b(j), where m = A003285(n) is the period of the
continued fraction of sqrt(n), and C = 2*a(n), for each nonsquare n; the same holds for the
numerators of the convergents. (A comment on the page says this was proved by J. Ritsema van
Eck, 2021.)

Conventions:
* a(n), for nonsquare n, is the least x such that x^2 - n*y^2 = 1 or -1 for some y ≥ 1
  (T. D. Noe's comment: the trivial solution y = 0 is excluded for nonsquare n). Square n
  (where a(n) = 1 by convention and the continued fraction of sqrt(n) terminates) are excluded:
  the claim is only made for nonsquare n.
* The convergents are Mathlib's `GenContFract.of (√n)`: `nums j` and `dens j` are the
  numerator and denominator of the j-th convergent, `nums 0 = ⌊√n⌋`, `dens 0 = 1`.
* The period m is the least m ≥ 1 with the partial denominators a_1, a_2, ... (Mathlib's
  `partDens`) periodic of period m; for sqrt(n) this sequence is purely periodic.
Checked by computation (exact integers) for all nonsquare n < 400 and indices j < 300 - 2m,
for numerators and denominators; a(n) matches the data of A006702.
-/

namespace OMA.S_oeis_a006702

/-- A006702(n) for nonsquare `n`: the least `x` with `x^2 - n*y^2 = ±1` for some `y ≥ 1`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {x : ℕ | ∃ y : ℕ, 1 ≤ y ∧
    ((x : ℤ) ^ 2 - n * (y : ℤ) ^ 2 = 1 ∨ (x : ℤ) ^ 2 - n * (y : ℤ) ^ 2 = -1)}

/-- A003285(n): the period of the continued fraction of `√n`. -/
noncomputable def period (n : ℕ) : ℕ :=
  sInf {m : ℕ | 1 ≤ m ∧ ∀ i : ℕ,
    (GenContFract.of (Real.sqrt n)).partDens.get? (i + m) =
      (GenContFract.of (Real.sqrt n)).partDens.get? i}

theorem main : ∀ n : ℕ, ¬ IsSquare n → ∀ j : ℕ,
    (GenContFract.of (Real.sqrt n)).dens (j + 2 * period n) =
      2 * (a n : ℝ) * (GenContFract.of (Real.sqrt n)).dens (j + period n) -
        (-1) ^ period n * (GenContFract.of (Real.sqrt n)).dens j ∧
    (GenContFract.of (Real.sqrt n)).nums (j + 2 * period n) =
      2 * (a n : ℝ) * (GenContFract.of (Real.sqrt n)).nums (j + period n) -
        (-1) ^ period n * (GenContFract.of (Real.sqrt n)).nums j := by
  sorry

end OMA.S_oeis_a006702
