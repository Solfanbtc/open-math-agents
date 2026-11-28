import Mathlib

/-!
# A071069: a(n) = min { A070923(k) | n^3 < k < (n+1)^3 }

Source: https://oeis.org/A071069
Credit: @Solfanbtc

A070923 (offset 0): `A070923(k)` is the smallest value `≥ 0` of the form `x^3 - k^2`
(`= ⌈k^(2/3)⌉^3 - k^2`). A071069 (offset 1): `a(n) = min { A070923(k) : n^3 < k < (n+1)^3 }`:
`2, 4, 11, 13, 7, 28, 47, …`.

Conjectures (OEIS comment): "Strong conjecture: for `n > 12`, `n^2/2 < a(n) < n^2`. Weak conjecture:
`a(n) > n` for any `n`." Both are stated, as the two parts of `main` (the first written
`n^2 < 2 a(n) ∧ a(n) < n^2`).

Status: both are FALSE.
* Strong: "The strong conjecture does not hold for `n = 23, 26, 28, 30, 36, 42, …`" (Lambert
  Klasen, Dec 17 2004, OEIS comment).
* Weak (not recorded in the entry): Elkies' example for Hall's conjecture,
  `x = 5853886516781223`, `y = 447884928428402042307918`, has `x^3 - y^2 = 1641843`; with
  `n = 76510695` one has `n^3 < y < (n+1)^3` and `(x-1)^3 < y^2`, so `A070923(y) = 1641843` and
  `a(76510695) ≤ 1641843 < 76510695` (checked with exact integer arithmetic in Python).
The conjectures are stated faithfully, as the source states them.
-/

namespace OMA.S_oeis_a071069

/-- A070923: the smallest `d ≥ 0` with `k^2 + d` a cube. -/
noncomputable def A070923 (k : ℕ) : ℕ := sInf {d : ℕ | ∃ x : ℕ, x ^ 3 = k ^ 2 + d}

/-- A071069: `a(n) = min { A070923(k) : n^3 < k < (n+1)^3 }`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf (((Finset.Ioo (n ^ 3) ((n + 1) ^ 3)).image A070923 : Finset ℕ) : Set ℕ)

/-- The strong and the weak conjecture of A071069 (both false, see the module docstring). -/
theorem main :
    (∀ n : ℕ, 12 < n → n ^ 2 < 2 * a n ∧ a n < n ^ 2) ∧ (∀ n : ℕ, 1 ≤ n → n < a n) := by
  sorry

end OMA.S_oeis_a071069
