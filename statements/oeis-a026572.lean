import Mathlib

/-!
# A026572: a(n) = T(n, n-3), T given by A026568

Source: https://oeis.org/A026572
Credit: @Solfanbtc

By A026568 (comment), `T(n, k)` is the number of integer strings `s(0), …, s(n)` with
`s(0) = 0`, `s(n) = n - k`, `|s(i) - s(i-1)| ≤ 1` if `s(i-1)` is even and `|s(i) - s(i-1)| = 1` if
`s(i-1)` is odd (`1 ≤ i ≤ n`). So `a(n) = T(n, n-3)` (offset 3) counts those strings with
`s(n) = 3`. Below, a string is given by its steps `c - 1` (`c : Fin 3`); the step out of an odd
position must be nonzero. This reproduces all 27 data terms `1, 2, 8, 19, 56, …`
(`n = 3, …, 29`); for `n < 3` the count is `0`.

The entry records two conjectures; both are stated, as the two parts of `main`:
1. (Mark van Hoeij, Oct 30 2011) the g.f. `∑ a(n) x^n` is
   `G = ((1 - x - 3x^2) ((x - 1)/(4x^2 + x - 1))^(1/2) - 1 + x + x^2) / (2x^3)`.
   (The coefficient of `x^n` in `G` is `a(n)`, with `a(n) = 0` for `n < 3`; Python check to
   `x^36`.) Here `(x-1)/(4x^2+x-1) = (1-x)/(1-x-4x^2)` and its square root is the power series with
   constant term `1`. Writing `A = ∑ a(n) x^n` and `P = 2x^3 A + 1 - x - x^2`, the claim `A = G` is
   equivalent to `P^2 (1 - x - 4x^2) = (1 - x - 3x^2)^2 (1 - x)` in `ℚ⟦x⟧`: `P` has constant term
   `1`, and a power series with constant term `1` whose square is `(1-x-3x^2)^2 (1-x)/(1-x-4x^2)`
   is unique (it is `(1-x-3x^2)` times the square root above). This form is stated.
2. (R. J. Mathar, Jun 23 2013) `(n+3) a(n) + (-3n-5) a(n-1) + 4(-n-1) a(n-2) + (13n-9) a(n-3)
   + (5n-9) a(n-4) + 6(-2n+7) a(n-5) = 0`, for `n ≥ 8` (so that all of `a(n), …, a(n-5)` are
   terms, offset 3). Python: holds for `8 ≤ n < 50`.
-/

namespace OMA.S_oeis_a026572

open PowerSeries

/-- The step value `c - 1 ∈ {-1, 0, 1}` encoded by `c : Fin 3`. -/
def step (c : Fin 3) : ℤ := (c : ℤ) - 1

/-- Position after the first `k` steps. -/
def pos {n : ℕ} (d : Fin n → Fin 3) (k : ℕ) : ℤ :=
  ∑ i : Fin n, if (i : ℕ) < k then step (d i) else 0

/-- A026572: strings from `0` to `3` in `n` steps, steps out of odd positions being `±1`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun d : Fin n → Fin 3 =>
    (∀ i : Fin n, Odd (pos d i) → step (d i) ≠ 0) ∧ pos d n = 3)).card

/-- The generating function `∑ a(n) x^n`. -/
def A : PowerSeries ℚ := PowerSeries.mk fun n => (a n : ℚ)

/-- van Hoeij's conjectured g.f. (in squared form) and Mathar's conjectured recurrence. -/
theorem main :
    ((2 * X ^ 3 * A + 1 - X - X ^ 2) ^ 2 * (1 - X - 4 * X ^ 2) =
      (1 - X - 3 * X ^ 2) ^ 2 * (1 - X)) ∧
    (∀ n : ℕ, 8 ≤ n →
      ((n : ℤ) + 3) * a n + (-3 * (n : ℤ) - 5) * a (n - 1) + 4 * (-(n : ℤ) - 1) * a (n - 2)
        + (13 * (n : ℤ) - 9) * a (n - 3) + (5 * (n : ℤ) - 9) * a (n - 4)
        + 6 * (-2 * (n : ℤ) + 7) * a (n - 5) = 0) := by
  sorry

end OMA.S_oeis_a026572
