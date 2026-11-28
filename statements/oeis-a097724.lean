import Mathlib

/-!
# A097724: Triangle read by rows: T(n,k) is the number of left factors of Motzkin paths without peaks, having length n and endpoint height k.

Source: https://oeis.org/A097724
Credit: @Solfanbtc

Conjecture (Peter Bala, Jun 26 2025): the row reverse triangle is the triangle of connection
constants for expressing `u(n, x+1)` as a linear combination of `u(k, x)`, `0 ≤ k ≤ n`, where
`u(n, x) = U(n, x/2)` with `U` the Chebyshev polynomials of the second kind. Example (row 7):
`u(7,x+1) = u(7,x) + 7 u(6,x) + 21 u(5,x) + 40 u(4,x) + 59 u(3,x) + 69 u(2,x) + 62 u(1,x) + 37`,
i.e. the coefficient of `u(k, x)` is `T(n, k)` (row 7 is `37, 62, 69, 59, 40, 21, 7, 1`).
So the claim is `u(n, x+1) = Σ_{k=0..n} T(n,k) u(k,x)` for all `n ≥ 0`.

Conventions. A left factor of a Motzkin path of length `n` is a word of `n` steps
`U = (1,1)` (`0`), `H = (1,0)` (`1`), `D = (1,-1)` (`2`) never going below height `0`; without
peaks means no `U` immediately followed by `D`. `T(n,k)` counts those ending at height `k`.
`u n = (U ℚ n).comp (X/2)` with Mathlib's `Polynomial.Chebyshev.U`.
Checked (python3, `n < 10`): the counts reproduce the data rows and the identity holds.
-/

namespace OMA.S_oeis_a097724

open Polynomial

/-- Height change of a step: `0 = U`, `1 = H`, `2 = D`. -/
def stepVal (s : Fin 3) : ℤ := if s = 0 then 1 else if s = 1 then 0 else -1

/-- Height after the first `i` steps of `w`. -/
def height {n : ℕ} (w : Fin n → Fin 3) (i : ℕ) : ℤ :=
  ∑ j : Fin n, if (j : ℕ) < i then stepVal (w j) else 0

/-- `w` is a left factor of a Motzkin path without peaks. -/
def IsPeaklessLeftFactor {n : ℕ} (w : Fin n → Fin 3) : Prop :=
  (∀ i ≤ n, 0 ≤ height w i) ∧
    ∀ i j : Fin n, (j : ℕ) = i + 1 → ¬ (w i = 0 ∧ w j = 2)

/-- A097724: `T(n,k)`, peakless Motzkin left factors of length `n` ending at height `k`. -/
noncomputable def T (n k : ℕ) : ℕ :=
  Set.ncard {w : Fin n → Fin 3 | IsPeaklessLeftFactor w ∧ height w n = k}

/-- `u(n, x) = U(n, x/2)`. -/
noncomputable def u (n : ℕ) : ℚ[X] := (Chebyshev.U ℚ (n : ℤ)).comp (C (1 / 2 : ℚ) * X)

/-- Bala's conjecture: `u(n, x+1) = Σ_{k=0..n} T(n,k) u(k,x)`. -/
theorem main : ∀ n : ℕ,
    (u n).comp (X + 1) = ∑ k ∈ Finset.range (n + 1), C (T n k : ℚ) * u k := by
  sorry

end OMA.S_oeis_a097724
