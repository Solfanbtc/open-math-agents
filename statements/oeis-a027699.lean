import Mathlib

/-!
# A027699: Evil primes: primes with even number of 1's in their binary expansion.

Source: https://oeis.org/A027699
Credit: @Solfanbtc

Comment of Vladimir Shevelev (Jun 01 2007, OEIS A027699): let pi_1(m) be the number of evil
primes <= m and pi_2(m) the number of odious primes (A027697, odd number of 1s in binary) <= m.
He conjectures
1. pi_1(m) <= pi_2(m) for all natural m except m = 5 and m = 6;
2. moreover pi_2(m) - pi_1(m) tends to infinity, with records at the primes
   m = 2, 13, 41, 61, 67, 79, 109, 131, 137, ...

Part 1 is not restated here: it follows elementarily from the upstream statement
`OeisA130911.conjecture` (FormalConjectures/OEIS/130911.lean: the partial sums over the first n
primes of +1 for odious, -1 for evil, are >= 0 for n > 3; pi_2 - pi_1 is constant between
consecutive primes, and the cases m < 7 are a finite check). `main` states part 2: the limit, and
the listed records. A record is an m >= 1 with pi_2(m) - pi_1(m) > pi_2(j) - pi_1(j) for every
j < m; the claim is that the records up to 137 are exactly the nine listed values (the list is
the beginning of the increasing sequence of records). Checked numerically up to 10^6: the records
begin 2, 13, 41, 61, 67, 79, 109, 131, 137, 173, ..., and part 1 holds with exceptions 5, 6 only.
-/

namespace OMA.S_oeis_a027699

open Filter

/-- Number of 1s in the binary expansion. -/
def binWeight (k : ℕ) : ℕ := (Nat.digits 2 k).count 1

/-- pi_2(m) - pi_1(m): odious primes ≤ m minus evil primes ≤ m. -/
def diff (m : ℕ) : ℤ :=
  (((Finset.range (m + 1)).filter fun p => p.Prime ∧ Odd (binWeight p)).card : ℤ) -
    (((Finset.range (m + 1)).filter fun p => p.Prime ∧ Even (binWeight p)).card : ℤ)

/-- `m` is a record of `diff`. -/
def IsRecord (m : ℕ) : Prop := 1 ≤ m ∧ ∀ j < m, diff j < diff m

theorem main :
    Tendsto diff atTop atTop ∧
    ∀ m : ℕ, m ≤ 137 → (IsRecord m ↔ m ∈ ({2, 13, 41, 61, 67, 79, 109, 131, 137} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a027699
