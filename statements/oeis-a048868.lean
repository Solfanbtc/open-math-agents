import Mathlib

/-!
# A048868: Numbers whose reduced residue system contains more primes than nonprimes.

Source: https://oeis.org/A048868
Credit: @Solfanbtc

The reduced residue system of `n` is taken, as in the entry's example, to be
`{k : 1 ≤ k ≤ n, gcd(k, n) = 1}` (for `n = 8`: `{1, 3, 5, 7}`); `1` counts as a nonprime.
`n` is a term when this set contains strictly more primes than nonprimes:
8, 12, 14, 16, 18, 20, ...

Conjecture (Michael De Vlieger, May 21 2017): all terms are even.

Sanity check (python): the definition below reproduces all 61 listed terms; there are 555 terms
up to 20000, none of them odd.
-/

namespace OMA.S_oeis_a048868

/-- The reduced residue system of `n`: `1 ≤ k ≤ n` with `gcd(k, n) = 1`. -/
def reducedResidues (n : ℕ) : Finset ℕ := (Finset.Icc 1 n).filter (fun k => Nat.Coprime k n)

/-- `n` belongs to A048868: more primes than nonprimes in its reduced residue system. -/
def InSeq (n : ℕ) : Prop :=
  ((reducedResidues n).filter (fun k => ¬ k.Prime)).card <
    ((reducedResidues n).filter (fun k => k.Prime)).card

/-- De Vlieger's conjecture: every term of A048868 is even. -/
theorem main : ∀ n : ℕ, InSeq n → Even n := by
  sorry

end OMA.S_oeis_a048868
