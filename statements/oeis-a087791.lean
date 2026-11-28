import Mathlib

/-!
# A087791: Indices n such that S^n(1) is an integer where S(x) = 3/2*ceiling(x).

Source: https://oeis.org/A087791
Credit: @Solfanbtc

`S x = (3/2) ⌈x⌉` on `ℚ`. A087791 lists, in increasing order (offset 0), the `k ≥ 0` such that
`S^[k] 1` is an integer: 0, 2, 5, 6, 7, 10, ... (`S 1 = 3/2`, `S (3/2) = 3`). Here
`a n = Nat.nth I n`, where `I` is the set of such `k`. Checked with python3 (exact rationals):
this reproduces the listed data, and `a(n) - 2n` = -1, -17, -13, 50 at `n = 100, 300, 500, 974`.

Conjecture (B. Cloitre): `a(n) = 2n + O(√n)`. `main` states `a(n) - 2n = O(√n)` as `n → ∞`.
-/

namespace OMA.S_oeis_a087791

open Filter Asymptotics Real

/-- `S x = (3/2) ⌈x⌉`. -/
def S (x : ℚ) : ℚ := 3 / 2 * (⌈x⌉ : ℚ)

/-- The indices `k` with `S^[k] 1` an integer. -/
def I : Set ℕ := {k | ∃ m : ℤ, S^[k] 1 = m}

/-- `a n`: the `n`-th such index (offset 0). -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth I n

theorem main :
    (fun n : ℕ => (a n : ℝ) - 2 * n) =O[atTop] fun n => sqrt (n : ℝ) := by
  sorry

end OMA.S_oeis_a087791
