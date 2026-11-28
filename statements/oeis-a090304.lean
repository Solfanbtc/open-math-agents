import Mathlib

/-!
# A090304: Indices of 0's in A090303.

Source: https://oeis.org/A090304
Credit: @Solfanbtc

A090303(n): starting from `n`, successively subtract 2, 3, 5, 7, 11, ...; A090303(n) is the
largest prime that arises, i.e. the largest prime of the form `n - (prime(1) + ... + prime(r))`
with `r ≥ 1`, or 0 if there is none (`n` itself is not considered: A090303(5) = 3).
So A090303(n) = 0 iff no `n - S(r)`, `r ≥ 1`, is prime, where `S(r)` is the sum of the first
`r` primes (when `S(r) ≥ n` the truncated difference is 0, which is not prime).
A090304 lists these `n ≥ 1`. We checked by computer that this gives the 214 terms of the
b-file, the last being 16866 (no more terms up to 10^9, C. R. Greathouse IV).

Conjecture (Amarnath Murthy, 2003): the sequence is finite.
-/

namespace OMA.S_oeis_a090304

/-- `S(r)`: the sum of the first `r` primes. -/
noncomputable def S (r : ℕ) : ℕ := ∑ i ∈ Finset.range r, Nat.nth Nat.Prime i

/-- A090304 is finite. -/
theorem main : {n : ℕ | 1 ≤ n ∧ ∀ r : ℕ, 1 ≤ r → S r < n → ¬ (n - S r).Prime}.Finite := by
  sorry

end OMA.S_oeis_a090304
