import Mathlib

/-!
# A137939: Number of 5-way intersections in the interior of a regular 6n-gon.

Source: https://oeis.org/A137939
Credit: @Solfanbtc

Conjecture (G. McRae, OEIS A137939, checked up to n = 210): "An n-gon with n = 30k has 5n points
where 6 or 7 diagonals meet and no interior point other than the center where more than 7
diagonals meet; if k is odd, then 6 diagonals meet in each of 4n points and 7 diagonals meet in
each of n points; if k is even, then no groups of exactly 6 diagonals meet in a point, while
exactly 7 diagonals meet in each of 5n points (all points interior excluding the center)."
The exact counts of k-fold intersection points of a regular polygon were studied by B. Poonen and
M. Rubinstein (arXiv:math/9508209), whose formulas for the numbers a_k(n) appear to cover this claim.

Model. The regular `n`-gon has vertices `vtx n j = exp(2πi j / n)`, `j < n`, in `ℂ`.
`mult n z` is the number of chords `[vtx n i, vtx n j]` (`i < j`) containing `z`. Chords include
the sides, but a non-vertex point on a side lies on no other chord, so for `m ≥ 2` the points with
`mult n z = m` that are not vertices are exactly the interior points where exactly `m` diagonals
meet. "Excluding the center" is `z ≠ 0`.

Checked with python3 (floating-point intersection of all diagonals): the 30-gon has 120 = 4·30
points of multiplicity 6 and 30 of multiplicity 7; the 60-gon has none of multiplicity 6 and
300 = 5·60 of multiplicity 7; no non-central point has multiplicity above 7 in either.
-/

namespace OMA.S_oeis_a137939

/-- The `j`-th vertex of the regular `n`-gon inscribed in the unit circle. -/
noncomputable def vtx (n : ℕ) (j : Fin n) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((j : ℕ) : ℂ) / n)

/-- The number of chords of the regular `n`-gon through `z`. -/
noncomputable def mult (n : ℕ) (z : ℂ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin n × Fin n)).filter
    (fun p => p.1 < p.2 ∧ z ∈ segment ℝ (vtx n p.1) (vtx n p.2))).card

/-- The non-central, non-vertex points where exactly `m` chords of the regular `n`-gon meet. -/
def pointsWith (n m : ℕ) : Set ℂ :=
  {z | z ≠ 0 ∧ z ∉ Set.range (vtx n) ∧ mult n z = m}

/-- McRae's conjecture on 6- and 7-fold intersection points of the regular `30k`-gon. -/
theorem main : ∀ k : ℕ, 1 ≤ k →
    (pointsWith (30 * k) 6 ∪ pointsWith (30 * k) 7).ncard = 5 * (30 * k) ∧
    (∀ z : ℂ, z ≠ 0 → z ∉ Set.range (vtx (30 * k)) → mult (30 * k) z ≤ 7) ∧
    (Odd k → (pointsWith (30 * k) 6).ncard = 4 * (30 * k) ∧
      (pointsWith (30 * k) 7).ncard = 30 * k) ∧
    (Even k → pointsWith (30 * k) 6 = ∅ ∧ (pointsWith (30 * k) 7).ncard = 5 * (30 * k)) := by
  sorry

end OMA.S_oeis_a137939
