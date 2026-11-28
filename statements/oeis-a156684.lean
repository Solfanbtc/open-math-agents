import Mathlib

/-!
# A156684: density of primitive Pythagorean triples with both legs below N

Source: https://oeis.org/A156684
Credit: @Solfanbtc

A156684 (offset 1): `a(N)` is the number of primitive Pythagorean triples `A^2 + B^2 = C^2`
with `0 < A < B < C`, `gcd(A, B) = 1`, and both legs less than `N` (i.e. `B < N`).
Data 0, 0, 0, 0, 1, 1, …; `a(14) = 2` from (3,4,5) and (5,12,13).

The entry: "it certainly appears that the density of the primitive triples with both legs less
than N tends towards (2/Pi^2)*log(1+sqrt(2)) = 0.1786... as N becomes large." Status: "The above
conjecture is true: see Lorenzo Sauras Altuzarra Link" (Feb 02 2026); it also follows from the
asymptotic of Benito and Varona quoted in the entry. `main` states the limit
`a(N)/N → (2/π^2) log(1 + √2)`.

Checked with python3: the definition reproduces the first 34 terms, and `a(3000)/3000 = 0.1780`
against `0.17860…`.
-/

namespace OMA.S_oeis_a156684

/-- A156684: the number of primitive Pythagorean triples with `0 < A < B < C` and `B < N`. -/
noncomputable def a (N : ℕ) : ℕ :=
  {t : ℕ × ℕ × ℕ | 0 < t.1 ∧ t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ t.1 ^ 2 + t.2.1 ^ 2 = t.2.2 ^ 2 ∧
    Nat.gcd t.1 t.2.1 = 1 ∧ t.2.1 < N}.ncard

open Filter Topology in
/-- The density of primitive Pythagorean triples with both legs below `N` is
`(2/π^2) log(1 + √2)`. -/
theorem main : Tendsto (fun N : ℕ => (a N : ℝ) / N) atTop
    (𝓝 (2 / Real.pi ^ 2 * Real.log (1 + Real.sqrt 2))) := by
  sorry

end OMA.S_oeis_a156684
