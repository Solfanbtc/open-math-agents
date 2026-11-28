import Mathlib

/-!
# A086811: scaled average of the n-th cyclotomic coefficient: integrality and nonnegativity

Source: https://oeis.org/A086811
Credit: @Solfanbtc

A086811 (offset 1; P. Moree): the average over all `m` of `a_m(k)`, the `k`-th coefficient of the
`m`-th cyclotomic polynomial, scaled by an explicit factor. The entry gives the explicit formula
(Moree and Hommersom 2003, Section 8.3): with `M_k = k * Product_{prime p <= k} p` and any prime
`q > k`, the `k`-th term (for `k ≥ 2`) is
`M_k * Sum_{d | M_k} (a_d(k) + a_{d q}(k)) / (2d)`. Data 0, 3, 6, 16, 45, 126, 224, 1344, …

The entry's conjectures, both stated in `main` (for `k ≥ 2`, the range of the formula; `a(1) = 0`):
* "When n is odd the n-th term is an integer. If n is even then twice the n-th term is an integer.
  Conjecturally (Y. Gallot) the n-th term is always an integer. For n <= 128 this has been
  verified numerically by Yves Gallot."
* "It is also an unproved conjecture due to H. Möller (1970) that no term of this sequence is
  negative."

Definitions. `a_m(k)` is `(Polynomial.cyclotomic m ℤ).coeff k` (Mathlib's `cyclotomic 1 = X - 1`,
the usual convention). We take `q` to be the least prime `> k`; the formula does not depend on
this choice. Checked with python3: the formula reproduces the listed terms for `2 ≤ k ≤ 11`, and
gives the same values with `q = 29` for `2 ≤ k ≤ 8`.
-/

namespace OMA.S_oeis_a086811

open Polynomial

/-- `M_k = k * Product_{prime p <= k} p`. -/
def bigM (k : ℕ) : ℕ := k * ∏ p ∈ (Finset.range (k + 1)).filter Nat.Prime, p

/-- The least prime `q > k`. -/
noncomputable def nextPrime (k : ℕ) : ℕ := sInf {q : ℕ | q.Prime ∧ k < q}

/-- The `k`-th term of A086811 (for `k ≥ 2`), by the explicit formula of the entry. -/
noncomputable def term (k : ℕ) : ℚ :=
  bigM k * ∑ d ∈ (bigM k).divisors,
    (((cyclotomic d ℤ).coeff k + (cyclotomic (d * nextPrime k) ℤ).coeff k : ℤ) : ℚ) / (2 * d)

/-- Gallot's integrality conjecture and Möller's nonnegativity conjecture for A086811. -/
theorem main : ∀ k : ℕ, 2 ≤ k → (∃ z : ℤ, term k = z) ∧ 0 ≤ term k := by
  sorry

end OMA.S_oeis_a086811
