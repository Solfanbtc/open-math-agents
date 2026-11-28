import Mathlib

/-!
# A133266: a(1) = 30; for n >= 2, choose smallest a(n) so that no sum of 2 or more terms equals a prime.

Source: https://oeis.org/A133266 (Robert G. Wilson v, 2008; conjecture by Chai Wah Wu,
Feb 15 2020; OEIS Foundation, CC BY-SA 4.0).
Credit: @Solfanbtc

Conjecture (OEIS): a(n+1) = a(n) + 30 for n >= 7.

Formalization notes.
* As in the Mathematica program of the entry, a(n) is the smallest k > a(n-1) such that, among
  a(1), ..., a(n-1), k, no sum of two or more distinct terms is prime. A sum of terms means a
  sum over a subset of the terms (each term used at most once), as in the program, which ranges
  over the nonempty subsets of the earlier terms and adds k.
* The sequence is given by its greedy specification `IsA133266`, and the conjecture is stated
  for every sequence meeting it. The specification determines a(1), a(2), ... uniquely (by
  induction, since each a(n) is a least element), and such a sequence exists: if T is the sum
  of a(1), ..., a(n-1), then k = (T+1)! > a(n-1) works, since every new sum S + k, with S a
  nonempty subset sum of the earlier terms (so 30 ≤ S ≤ T), is a proper multiple of S. So the statement is
  not vacuous.
* Indices are the OEIS indices (offset 1); the value of `a 0` is irrelevant.
* A python computation reproduces the 30 listed terms and confirms the conjecture for the
  first 150 terms.
-/

namespace OMA.S_oeis_a133266

/-- No sum of two or more distinct elements of `s` is prime. -/
def NoPrimeSums (s : Finset ℕ) : Prop :=
  ∀ t ⊆ s, 2 ≤ t.card → ¬ (∑ x ∈ t, x).Prime

/-- The greedy specification of A133266 (OEIS indices n ≥ 1). -/
def IsA133266 (a : ℕ → ℕ) : Prop :=
  a 1 = 30 ∧
  ∀ n, 2 ≤ n →
    a (n - 1) < a n ∧
    NoPrimeSums ((Finset.Icc 1 n).image a) ∧
    ∀ k, a (n - 1) < k → k < a n → ¬ NoPrimeSums (insert k ((Finset.Icc 1 (n - 1)).image a))

theorem main : ∀ a : ℕ → ℕ, IsA133266 a → ∀ n, 7 ≤ n → a (n + 1) = a n + 30 := by
  sorry

end OMA.S_oeis_a133266
