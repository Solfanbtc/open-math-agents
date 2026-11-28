import Mathlib

/-!
# A000531: Maximum number of (2n + 1)-sided cyclic polygons with specified side lengths.

Source: https://oeis.org/A000531
Credit: @Solfanbtc

Simon Norton's conjectured definition (OEIS A000531, May 14 2001): let
`0 < a₁ < a₂ < ... < a_{2n} < 1`; count the ways in which one can add or subtract all the `aᵢ`
to get an odd number. For `n = 2` the options are `a₁+a₂+a₃+a₄ = 1` or `3`, changing the sign of
any one `aᵢ` and getting `1`, or `-a₁-a₂+a₃+a₄ = 1`: a total of `7 = a(2)`.

Reading used here (the one the worked example fixes): a "way" is a pair (choice of signs, odd
value) that is attainable by SOME admissible `a₁ < ... < a_{2n}` (for one fixed generic choice of
the `aᵢ` no signed sum is an integer at all). The example counts only positive odd values
(`a₁+a₂+a₃+a₄ = 1` or `3`, not `-1`, `-3`); equivalently, sign choices are taken up to a global
sign. A sign choice is encoded by the set `S` of indices that are subtracted.

The sequence is given by its closed form `a(n) = (2n+1)/2 · C(2n,n) - 2^(2n-1)` (offset 1:
`1, 7, 38, 187, 874, ...`), which is Robbins' formula for the degree of the generalized Heron
polynomial of a cyclic `(2n+1)`-gon, the defining property of A000531.
A python check of this reading (the attainable values of a signed sum form an open interval
whose endpoints are the extreme values at the vertices `(0,…,0,1,…,1)`) gives
`1, 7, 38, 187, 874, 3958` for `n = 1..6`, matching the closed form.

Norton's second, geometric conjecture in the same comment (uniqueness of the cyclic polygon
for each winding number and set of retrograde sides) is not stated here.
-/

namespace OMA.S_oeis_a000531

/-- A000531 (offset 1): `a(n) = (2n+1)·C(2n,n)/2 - 2^(2n-1)`. -/
def a (n : ℕ) : ℕ := (2 * n + 1) * Nat.choose (2 * n) n / 2 - 2 ^ (2 * n - 1)

/-- The "ways": pairs `(S, k)` with `S` the set of subtracted indices and `k` a positive odd
number such that `∑_{i ∉ S} aᵢ - ∑_{i ∈ S} aᵢ = k` for some `0 < a₁ < ... < a_{2n} < 1`. -/
def ways (n : ℕ) : Set (Finset (Fin (2 * n)) × ℕ) :=
  {p | Odd p.2 ∧ ∃ x : Fin (2 * n) → ℝ, StrictMono x ∧ (∀ i, 0 < x i ∧ x i < 1) ∧
    ∑ i, (if i ∈ p.1 then -x i else x i) = (p.2 : ℝ)}

theorem main : ∀ n : ℕ, 1 ≤ n → (ways n).ncard = a n := by
  sorry

end OMA.S_oeis_a000531
