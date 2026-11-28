import Mathlib

/-!
# A140934: Number of 2 X 11 matrices with elements in 0..n with each row and each column in nondecreasing order. 2,11,n can be permuted, see

Source: https://oeis.org/A140934
Credit: @Solfanbtc

`a(n)` (offset 0) is the number of `2 × 11` matrices with entries in `{0, ..., n}` whose rows and
columns are nondecreasing.

Conjecture (B. Berselli, May 07 2012, OEIS A140934):
`a(n) = ((n + 12) / (12 n + 12)) · C(n + 11, 11)^2` for all `n ≥ 0`.
Berselli's other conjectures in the entry (the generating function
`(1 + 55x + 825x^2 + ... + 55x^9 + x^10)/(1 - x)^23`, the 12th column of the Narayana triangle
A001263, and the product formula of Sep 2016) follow from this closed form by algebra.
Such matrices are plane partitions fitting in a `2 × 11 × n` box, so this closed form should
follow from MacMahon's box formula (see also Liu–Xin–Zhang, arXiv:2412.18744); we state the
conjecture as it appears in the entry.

Checked with python3: a direct count with this definition and the closed form both reproduce
all 21 listed terms (n = 0..20).
-/

namespace OMA.S_oeis_a140934

/-- `a n`: the number of `2 × 11` matrices with entries in `0..n` and nondecreasing rows and
columns. -/
def a (n : ℕ) : ℕ :=
  Fintype.card {M : Fin 2 → Fin 11 → Fin (n + 1) //
    (∀ i : Fin 2, ∀ j j' : Fin 11, j ≤ j' → M i j ≤ M i j') ∧
    (∀ i i' : Fin 2, ∀ j : Fin 11, i ≤ i' → M i j ≤ M i' j)}

/-- Berselli's conjectured closed form for A140934. -/
theorem main : ∀ n : ℕ,
    (a n : ℚ) = ((n : ℚ) + 12) / (12 * (n : ℚ) + 12) * ((Nat.choose (n + 11) 11 : ℕ) : ℚ) ^ 2 := by
  sorry

end OMA.S_oeis_a140934
