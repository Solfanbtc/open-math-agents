import Mathlib

/-!
# A085780: Numbers that are a product of 2 triangular numbers.

Source: https://oeis.org/A085780
Credit: @Solfanbtc

`S` is the set of numbers `T(i) T(j)` with `T(k) = k (k+1) / 2` and `i, j ≥ 0` (the data starts
0, 1, 3, 6, 9, ...). `count x` is the number of elements of `S` in `[0, x]`.

Conjecture (C. R. Greathouse IV, 2024): "There are about `sqrt(x) log(x)` terms up to `x`".
"About" is read as order of magnitude, with no constant specified: `count x = Θ(√x log x)` as
`x → ∞`. `main` states this. (python3: `count x / (√x log x)` = 0.465, 0.479, 0.486, 0.488 at
`x = 10^6, 10^8, 10^10, 10^11`. So the ratio approaches a constant near 1/2, not 1, and the
stronger reading `count x ~ √x log x` looks false.)
-/

namespace OMA.S_oeis_a085780

open Filter Asymptotics Real

/-- Products of two triangular numbers. -/
def S : Set ℕ := {n | ∃ i j : ℕ, n = (i * (i + 1) / 2) * (j * (j + 1) / 2)}

open Classical in
/-- Number of elements of `S` that are at most `x`. -/
noncomputable def count (x : ℕ) : ℕ := ((Finset.range (x + 1)).filter (· ∈ S)).card

theorem main :
    (fun x : ℕ => (count x : ℝ)) =Θ[atTop] fun x => sqrt (x : ℝ) * log (x : ℝ) := by
  sorry

end OMA.S_oeis_a085780
