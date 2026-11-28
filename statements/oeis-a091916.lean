import Mathlib

/-!
# A091916: Maximum of odd products of partitions of n.

Source: https://oeis.org/A091916
Credit: @Solfanbtc

`a(n)` is the maximum of the products of the parts over the partitions of `n` whose product is
odd, i.e. whose parts are all odd (for `n = 5`: 5, 3·1·1, 1·1·1·1·1 give the odd products 5, 3, 1,
so `a(5) = 5`): 1, 1, 1, 3, 3, 5, 9, 9, 15, 27, ... (offset 0; the empty partition gives `a(0) = 1`).

Conjecture (Ralf Stephan, Dec 02 2004): for `n > 5`, `a(n+3) = 3 a(n)`.

Encoding: partitions of `n` are Mathlib's `Nat.Partition n`; `a n` is the supremum (a maximum,
over a nonempty finite set: the partition into ones) of the products over partitions with all
parts odd.

Sanity check (python): the definition gives all 34 listed terms; the relation holds for every
`n ≤ 117` except `n = 2`.
-/

namespace OMA.S_oeis_a091916

/-- A091916. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Nat.Partition n)).filter (fun p => ∀ i ∈ p.parts, Odd i)).sup
    (fun p => p.parts.prod)

/-- Stephan's conjecture. -/
theorem main : ∀ n : ℕ, 5 < n → a (n + 3) = 3 * a n := by
  sorry

end OMA.S_oeis_a091916
