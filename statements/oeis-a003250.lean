import Mathlib

/-!
# A003250: The number m such that A001950(m) = A003231(A003234(n)).

Source: https://oeis.org/A003250
Credit: @Solfanbtc

With `φ = (1 + √5)/2`:
* A001950 (upper Wythoff): `W(m) = ⌊m φ²⌋`;
* A003231: `C(n) = ⌊n (5 + √5)/2⌋`;
* A003234 (`s` in Carlitz): the increasing sequence of `k ≥ 1` with `C(W(k)) = W(C(k)) - 1`:
  `3, 8, 11, 16, 19, 21, ...`;
* A003250 (`z` in Carlitz): `a(n)` is the `m` with `W(m) = C(s(n))`: `4, 11, 15, 22, 26, ...`.

Conjecture (Eric M. Schmidt, Aug 14 2014, in the entry): `a(n) = ⌊(3 - φ) s(n)⌋`.

Since `W` is strictly increasing (injective), `a(n) = ⌊(3 - φ) s(n)⌋` is equivalent to
`W(⌊(3 - φ) s(n)⌋) = C(s(n))`, which is the form stated (it also asserts that the `m` in the
definition of `a(n)` exists). A python3 check with exact integer arithmetic: the definitions
reproduce the data of A003234 and A003250, and the conjecture holds for all 55277 terms with
`s(n) < 200000`.

Conventions:
* Offsets are 1: `s n = Nat.nth (property) (n - 1)` for `n ≥ 1`.
* Floors are taken in `ℝ` with `Int.floor` and converted with `Int.toNat` (all values are
  nonnegative).
-/

namespace OMA.S_oeis_a003250

/-- The golden ratio. -/
noncomputable def φ : ℝ := (1 + Real.sqrt 5) / 2

/-- A001950: `W m = ⌊m φ²⌋`. -/
noncomputable def W (m : ℕ) : ℕ := (Int.floor ((m : ℝ) * φ ^ 2)).toNat

/-- A003231: `C n = ⌊n (5 + √5) / 2⌋`. -/
noncomputable def C (n : ℕ) : ℕ := (Int.floor ((n : ℝ) * (5 + Real.sqrt 5) / 2)).toNat

/-- The defining property of A003234. -/
def IsS (k : ℕ) : Prop := 1 ≤ k ∧ C (W k) + 1 = W (C k)

/-- A003234: `s n` is the `n`-th `k ≥ 1` with `C(W(k)) = W(C(k)) - 1`. -/
noncomputable def s (n : ℕ) : ℕ := Nat.nth IsS (n - 1)

/-- Schmidt's conjecture: `A003250(n) = ⌊(3 - φ) A003234(n)⌋`, i.e. `W(⌊(3 - φ) s(n)⌋) = C(s(n))`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    W (Int.floor ((3 - φ) * (s n : ℝ))).toNat = C (s n) := by
  sorry

end OMA.S_oeis_a003250
