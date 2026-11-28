import Mathlib

/-!
# A134650: Numbers that are the sum of two consecutive primes (i.e., in A001043) but are not the sum of two sums of two consecutive primes.

Source: https://oeis.org/A134650
Credit: @Solfanbtc

Claim (entry comment): this sequence is finite. The entry only adds that the listed terms
5, 8, 12, 18, 52, 100, 946 "may be" complete, and that a(8), if it exists, is greater than
20100000 (R. J. Mathar); only finiteness is conjectured. Reference: R. K. Guy, ed., Unsolved
Problems, Western Number Theory Meeting, Las Vegas, 1988.

Conventions. A001043 is the set of p_k + p_(k+1) for consecutive primes (p_0 = 2, so 2 + 3 = 5
is included). A "sum of two sums of two consecutive primes" is s + t with s, t in A001043, not
necessarily distinct (the entry's Maple program allows s = t). A python check with exactly these
conventions, over the sums of consecutive primes up to 4·10^6, gives the listed terms
5, 8, 12, 18, 52, 100, 946 and no others.
-/

namespace OMA.S_oeis_a134650

/-- A001043: sums of two consecutive primes. -/
def ConsecPrimeSum (n : ℕ) : Prop := ∃ k : ℕ, n = Nat.nth Nat.Prime k + Nat.nth Nat.Prime (k + 1)

/-- A134650 as a set. -/
def A134650 : Set ℕ :=
  {n | ConsecPrimeSum n ∧ ¬ ∃ s t : ℕ, ConsecPrimeSum s ∧ ConsecPrimeSum t ∧ n = s + t}

theorem main : A134650.Finite := by
  sorry

end OMA.S_oeis_a134650
