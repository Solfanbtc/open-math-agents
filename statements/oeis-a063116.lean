import Mathlib

/-!
# A063116: Dimension of the space of weight 2n cusp forms for Gamma_0(48)

Source: https://oeis.org/A063116
Credit: @Solfanbtc

`a(n) = dim_ℂ S_{2n}(Γ₀(48))` (offset 1): `3, 18, 34, 50, 66, …`; the entry records
`a(n) = 2(8n - 7)` for `n > 1` (Colin Barker, from the g.f.).

Conjecture (David James Sycamore, Sep 12 2019, OEIS comment): for `n ≥ 2`, `a(n)` is the
difference between the greater elements of successive pairs of odd triangular numbers,
`A(B(n-1)+1) - A(B(n-2)+1)`, where `A = A000217` (`A(m) = m(m+1)/2`) and `B = A016813`
(`B(m) = 4m + 1`); "this reduces to `a(n) = 2(8n - 7)`". E.g. `(1, 3), (15, 21)` are the first
consecutive pairs of odd triangular numbers, and `21 - 3 = 18 = a(2)`.

Stated with Mathlib's cusp forms: `Module.finrank ℂ (CuspForm (Gamma0 48) (2n))` equals
`A(B(n-1)+1) - A(B(n-2)+1)` for all `n ≥ 2`. (The right side is `16n - 14 = 2(8n - 7)`.)
-/

namespace OMA.S_oeis_a063116

/-- A000217: triangular numbers. -/
def A000217 (m : ℕ) : ℕ := m * (m + 1) / 2

/-- A016813: `4m + 1`. -/
def A016813 (m : ℕ) : ℕ := 4 * m + 1

/-- Sycamore's conjecture: `dim S_{2n}(Γ₀(48)) = A(B(n-1)+1) - A(B(n-2)+1)` for `n ≥ 2`. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    (Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 48) (2 * n : ℤ)) : ℤ) =
      (A000217 (A016813 (n - 1) + 1) : ℤ) - A000217 (A016813 (n - 2) + 1) := by
  sorry

end OMA.S_oeis_a063116
