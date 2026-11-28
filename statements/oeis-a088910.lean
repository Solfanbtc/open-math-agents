import Mathlib

/-!
# A088910: few signed squares of distinct primes

Source: https://oeis.org/A088910
Credit: @Solfanbtc

`a(n)` (offset 0) is the (conjectured) minimal number `k` of terms in a representation
`n = ∑_{i=1}^{k} e_i p_i^2` with distinct primes `p_i` and signs `e_i = ±1`: `4, 3, 4, 4, 1, 2, 5, …`
(e.g. `0 = 7^2 - 11^2 - 17^2 + 19^2`, `6 = -(2^2) + 3^2 + 7^2 + 11^2 - 13^2`).

Conjecture (Hugo Pfoertner, OEIS comment): all sequence terms are `≤ 5`, i.e. every `n ≥ 0` has
such a representation with `1 ≤ k ≤ 5` terms. A representation is a nonempty finite set `S` of
primes (distinct by construction) and signs `e : ℕ → ℤ` with `e p = ±1` on `S`.
-/

namespace OMA.S_oeis_a088910

/-- Every natural number is a signed sum of the squares of at most 5 distinct primes. -/
theorem main : ∀ n : ℕ, ∃ S : Finset ℕ, 1 ≤ S.card ∧ S.card ≤ 5 ∧ (∀ p ∈ S, p.Prime) ∧
    ∃ e : ℕ → ℤ, (∀ p ∈ S, e p = 1 ∨ e p = -1) ∧ ∑ p ∈ S, e p * (p : ℤ) ^ 2 = n := by
  sorry

end OMA.S_oeis_a088910
