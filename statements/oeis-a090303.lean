import Mathlib

/-!
# A090303: largest prime of the form n - (2 + 3 + 5 + ⋯ + prime(r))

Source: https://oeis.org/A090303
Credit: @Solfanbtc

Begin with `n` and consider the numbers obtained by successively subtracting `2, 3, 5, 7, 11, …`,
i.e. `n - S(r)` for `r ≥ 1`, where `S(r) = prime(1) + ⋯ + prime(r)` (A007504: `2, 5, 10, 17, …`);
`a(n)` (offset 1) is the largest prime among them, or `0` if there is none:
`0, 0, 0, 2, 3, 0, 5, 3, 7, …` (`n` itself is not counted: `a(5) = 3`; this reproduces all 80 data
terms).

Conjecture (OEIS comment): there are finitely many zeros in this sequence, i.e. for all but finitely
many `n` some `n - S(r)`, `r ≥ 1`, `S(r) < n`, is prime. (Python: 214 zeros below `2·10^5`, the last
at `n = 16866`.) With Mathlib's 0-indexed primes, `S(r) = ∑_{i<r} Nat.nth Nat.Prime i`.
-/

namespace OMA.S_oeis_a090303

/-- `S(r) = prime(1) + ⋯ + prime(r)`. -/
noncomputable def S (r : ℕ) : ℕ := ∑ i ∈ Finset.range r, Nat.nth Nat.Prime i

/-- `a(n) = 0`: no `n - S(r)` with `r ≥ 1` and `S(r) < n` is prime. -/
def IsZero (n : ℕ) : Prop := ∀ r : ℕ, 1 ≤ r → S r < n → ¬ (n - S r).Prime

/-- A090303 has finitely many zeros. -/
theorem main : {n : ℕ | 1 ≤ n ∧ IsZero n}.Finite := by
  sorry

end OMA.S_oeis_a090303
