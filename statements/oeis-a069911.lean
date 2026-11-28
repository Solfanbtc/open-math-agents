import Mathlib

/-!
# A069911: Expansion of Product_{i in A069909} 1/(1 - x^i).

Source: https://oeis.org/A069911 (and https://oeis.org/A069909, https://oeis.org/A035457)
Credit: @Solfanbtc

A069909 is the set of numbers `≡ ±1, ±4, ±6, ±7 (mod 16)`, and
`∑ a(n) x^n = ∏_{i ∈ A069909} 1/(1 - x^i)`, so `a(n)` is the number of partitions of `n` into
parts from A069909: 1, 1, 1, 1, 2, 2, 3, 4, 5, 6, 8, ... (offset 0).
A035457(k) is the number of partitions of `k` into parts of the form `4j + 2`
(g.f. `1/∏_{j≥0} (1 - x^(4j+2))`, offset 0, A035457(0) = 1).

Conjecture (George Beck, Aug 19 2017): "Let b(k) be the convolution inverse of A035457,
k = 1, 2, 3, ...; then a(n) = -b(4n+3), n = 0, 1, 2, 3, ...".

Indexing: the convolution inverse of A035457 is the coefficient sequence of
`(∑ A035457(k) x^k)⁻¹ = ∏_{j≥0} (1 - x^(4j+2))`, which vanishes at every odd power of `x`.
Beck indexes `b` from `k = 1`, i.e. `b(k)` is the coefficient of `x^(k-1)`; so
`b(4n+3)` is the coefficient of `x^(4n+2)`. (With `b(k)` the coefficient of `x^k`, `b(4n+3) = 0`
and the claim would fail at `n = 0`; python confirms the offset-1 reading for `n < 200` and that
the offset-0 reading fails.)

Sanity check (python): the partition count reproduces all 57 listed terms of A069911, and
`a(n) = -[x^(4n+2)] (∑ A035457(k) x^k)⁻¹` for all `n < 200`.
-/

namespace OMA.S_oeis_a069911

/-- `a(n)`: partitions of `n` into parts `≡ ±1, ±4, ±6, ±7 (mod 16)`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun p : Nat.Partition n =>
    ∀ i ∈ p.parts, i % 16 ∈ ({1, 4, 6, 7, 9, 10, 12, 15} : Finset ℕ))).card

/-- A035457: partitions of `k` into parts of the form `4j + 2`. -/
def A035457 (k : ℕ) : ℕ :=
  (Finset.univ.filter (fun p : Nat.Partition k => ∀ i ∈ p.parts, i % 4 = 2)).card

/-- The generating function of A035457. -/
noncomputable def gA : PowerSeries ℚ := PowerSeries.mk fun k => (A035457 k : ℚ)

/-- Beck's conjecture: `a(n) = -b(4n+3)`, where `b(k)` is the coefficient of `x^(k-1)` in the
convolution inverse of A035457. -/
theorem main : ∀ n : ℕ, (a n : ℚ) = -PowerSeries.coeff (4 * n + 2) gA⁻¹ := by
  sorry

end OMA.S_oeis_a069911
