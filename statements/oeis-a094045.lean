import Mathlib

/-!
# A094045: Alternate composite and prime numbers not included earlier such that every concatenation of a pair of terms is a prime: a(2n) is prime and a(2n-1) is nonprime.

Source: https://oeis.org/A094045
Credit: @Solfanbtc

The sequence: `a(1) = 1`; for `k ≥ 2`, `a(k)` is the least positive integer not among
`a(1), ..., a(k-1)` such that the decimal concatenation `a(k-1) ‖ a(k)` is prime, where `a(k)`
must be prime when `k` is even and nonprime when `k` is odd (this matches the entry's
Mathematica program; the definition reproduces all 64 terms of %S, %T, %U).

The entry's comment says: *Conjecture: 2 and 5 are the only two nonmembers.*
Taken literally this fails trivially: every term `a(k)` with `k ≥ 2` is the last block of
the prime `a(k-1) ‖ a(k)` (which exceeds 10), so its last digit is 1, 3, 7 or 9; hence no
even number and no multiple of 5 (e.g. 4, 6, 10, 15) is ever a term. The minimal fix, which is
the form of the analogous conjecture in the sister entry A094044 (R. Israel: all members of
A045572 are in the sequence), is: every positive integer coprime to 10 is a term. Among primes
this says exactly that 2 and 5 are the only nonmembers. Since no step of the sequence is known
to always succeed, the statement also asserts that every step up to the occurrence actually
finds a term (`a j ≠ 0`; a failed search is encoded as `0`, which is never a genuine term).
-/

namespace OMA.S_oeis_a094045

/-- Decimal concatenation `x ‖ y` (for `y ≥ 1`). -/
def concat (x y : ℕ) : ℕ := x * 10 ^ (Nat.digits 10 y).length + y

/-- The candidates for the `k`-th term, given the previous terms `prev` (most recent first):
positive integers not used before, prime if `k` is even and nonprime if `k` is odd, whose
concatenation after the previous term is prime. -/
def candidates (prev : List ℕ) (k : ℕ) : Set ℕ :=
  {q | 0 < q ∧ q ∉ prev ∧ (Even k ↔ q.Prime) ∧ (concat (prev.headD 0) q).Prime}

/-- `terms n = [a(n), ..., a(1)]`; a failed search (no candidate) gives `0`. -/
noncomputable def terms : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | (n + 2) => sInf (candidates (terms (n + 1)) (n + 2)) :: terms (n + 1)

/-- `a k` is the `k`-th term of A094045 (`k ≥ 1`). -/
noncomputable def a (k : ℕ) : ℕ := (terms k).headD 0

/-- Corrected conjecture of A094045: every positive integer coprime to 10 (in particular every
prime other than 2 and 5) occurs in the sequence, all steps up to its occurrence being defined. -/
theorem main :
    ∀ n : ℕ, 0 < n → Nat.Coprime n 10 →
      ∃ k : ℕ, 1 ≤ k ∧ a k = n ∧ ∀ j, 1 ≤ j → j ≤ k → a j ≠ 0 := by
  sorry

end OMA.S_oeis_a094045
