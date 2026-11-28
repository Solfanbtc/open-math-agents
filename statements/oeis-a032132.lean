import Mathlib

/-!
# A032132: Number of series-reduced dyslexic planted planar trees with n leaves.

Source: https://oeis.org/A032132
Credit: @Solfanbtc

Conjecture (Petros Hadjicostas, Jan 17 2018, in A032132). Let `b(m, n)` be the number of
A-clusters with `m` cells and `n` outside edges not counting the root edge (Devadoss and Read,
*Cellular Structures Determined by Polygons and Trees*, Ann. Combin. 5 (2001), Section 3), and
`B(x, y) = ∑ b(m, n) x^m y^n`. Then, apparently, `b(2, n) = A024206(n - 1)` for `n ≥ 2`,
where `A024206(k) = ⌊(k + 1)² / 4⌋ - 1`; that is, `b(2, n) = ⌊n² / 4⌋ - 1`.

Conventions. The A-clusters themselves are not formalized; `B` is characterized by the
functional equation that Devadoss and Read prove (their Eq. (3.1), with the factor `x`
restored as explained in the OEIS comment):
`B(x,y) = y + (x/2) (B(x,y)² / (1 - B(x,y)) + (1 + B(x,y)) B(x²,y²) / (1 - B(x²,y²)))`.
Here `x = X 0`, `y = X 1` in `MvPowerSeries (Fin 2) ℚ`, and `sub2 B = B(x², y²)`.
The equation is stated with denominators cleared:
`2 (B - y) (1 - B) (1 - B(x²,y²)) = x (B² (1 - B(x²,y²)) + (1 + B) B(x²,y²) (1 - B))`.
Together with `B(0,0) = 0` (true for the cluster series, and needed because clearing the
denominators would otherwise admit spurious solutions such as `B = 1`), this has exactly one
solution, so `main` quantifies over all such `B`; `1 - B` and `1 - B(x²,y²)` are then
invertible and the cleared equation is equivalent to Eq. (3.1).

Small cases checked numerically: solving the equation reproduces Table 2 of Devadoss and Read
(`B = y + x y² + (x² + x) y³ + (2x³ + 3x² + x) y⁴ + …`), `∑_m b(m, n) = A032132(n)` for
`n ≤ 14`, and `b(2, n) = 0, 1, 3, 5, 8, 11, 15, …` `= ⌊n²/4⌋ - 1` for `2 ≤ n ≤ 14`.
-/

namespace OMA.S_oeis_a032132

open MvPowerSeries

/-- `sub2 B = B(x², y²)`: the coefficient of `x^i y^j` is that of `x^(i/2) y^(j/2)` in `B`
when `i` and `j` are both even, and `0` otherwise. -/
noncomputable def sub2 (B : MvPowerSeries (Fin 2) ℚ) : MvPowerSeries (Fin 2) ℚ :=
  fun e => if ∀ i, Even (e i) then B (Finsupp.mapRange (· / 2) (Nat.zero_div 2) e) else 0

/-- Hadjicostas' conjecture: `b(2, n) = A024206(n - 1) = ⌊n² / 4⌋ - 1` for `n ≥ 2`. -/
theorem main :
    ∀ B : MvPowerSeries (Fin 2) ℚ, B 0 = 0 →
    2 * (B - X 1) * (1 - B) * (1 - sub2 B) =
      X 0 * (B ^ 2 * (1 - sub2 B) + (1 + B) * sub2 B * (1 - B)) →
    ∀ n : ℕ, 2 ≤ n →
      B (Finsupp.single 0 2 + Finsupp.single 1 n) = ((n ^ 2 / 4 : ℕ) : ℚ) - 1 := by
  sorry

end OMA.S_oeis_a032132
