import Mathlib

/-!
# A099501: Least number of members in a subset of integers in the interval [n^2+1, (n+1)^2-1] whose product is twice a square.

Source: https://oeis.org/A099501
Credit: @Solfanbtc

Conjecture (entry comment): "Granville and Selfridge conjecture that a(n) <= 3 for all n."
Reference: A. Granville and J. Selfridge, Product of integers in an interval, modulo squares,
Electron. J. Combin. 8(1) (2001), https://doi.org/10.37236/1549.

Formalization. For every `n ≥ 1` (offset 1) there is a set `S` of integers in
`[n^2 + 1, (n+1)^2 - 1]` with at most 3 elements whose product is twice a square. (The empty
product 1 is not twice a square, so `S` is automatically nonempty; the existence of such an
`S` with at most 3 elements is exactly "a(n) is defined and a(n) ≤ 3".)
Checked with python3: the least such size reproduces the 105 data terms 1, 1, 3, 1, 1, 2, ...
-/

namespace OMA.S_oeis_a099501

theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ S : Finset ℕ, S ⊆ Finset.Icc (n ^ 2 + 1) ((n + 1) ^ 2 - 1) ∧
      S.card ≤ 3 ∧ ∃ m : ℕ, ∏ s ∈ S, s = 2 * m ^ 2 := by
  sorry

end OMA.S_oeis_a099501
