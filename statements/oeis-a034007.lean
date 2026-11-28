import Mathlib

/-!
# A034007: First differences of A045891.

Source: https://oeis.org/A034007
Credit: @Solfanbtc

Two conjectures of Gregory L. Simay (OEIS A034007, comments, Feb 2018):

* Conjecture 1: For compositions of n+k-1, a(n) is the number of runs of 1 of length k.
  Example: among the compositions of 4+2-1 = 5 there are a(4) = 4 runs of two 1's.
* Conjecture 2: More generally, let R(n,m,k) be the number of runs of k m's in all
  compositions of n. Then
  R(n,m,k) = A045623(n-m*k) - 2*A045623(n-m*(k+1)) + A045623(n-m*(k+2)).
  Example: R(7,1,1) = 144 - 2*64 + 28 = 44 = a(7).

Conventions (checked by brute force in Python for n < 15, 1 ≤ m, k ≤ 5):
* A run of k m's in a composition (a list of positive parts) is a maximal block of exactly k
  consecutive parts equal to m (the example counts 1,2,[1,1] and excludes blocks of three 1's).
  R(n,m,k) adds, over all compositions of n (Mathlib's `Composition n`), the number of such
  blocks. Here m ≥ 1 and k ≥ 1.
* Indexing: the comments index the terms of A034007 from 1 (the data begins 1, 0, 2, 4, 9, 20,
  44, ... with offset 0, and the comments call 4 = a(4) and 44 = a(7)). With the OEIS offset 0,
  i.e. `a 0 = 1, a 1 = 0, a 2 = 2, a 3 = 4`, Conjecture 1 reads R(n+k-1, 1, k) = a(n-1) for all
  n ≥ 1, k ≥ 1 (this is the minimal fix: with the offset-0 reading R(n+k-1,1,k) = a(n) fails
  for every n, e.g. R(4,1,1) = 4 ≠ 9 = a(4); with the shift it holds in all checked cases).
  Likewise in Conjecture 2 the value 44 is a(6) at offset 0; Conjecture 2 itself does not
  involve a.
* A045623(n) is the number of 1's in all compositions of n+1 (its OEIS definition), extended by
  0 at negative indices (needed when n < m*(k+2); with this convention Conjecture 2 holds in all
  checked cases, including n < m*k where both sides are 0).
* A045891 is the sequence of first differences of A045623 (A045891(0) = A045623(0) = 1), and
  A034007 the first differences of A045891; with the zero extension,
  a(n) = A045623(n) - 2*A045623(n-1) + A045623(n-2). Check: 1, 0, 2, 4, 9, 20, 44, ...
-/

namespace OMA.S_oeis_a034007

/-- The number of maximal blocks of exactly `k` consecutive entries equal to `m` in `l`. -/
def runCount (l : List ℕ) (m k : ℕ) : ℕ :=
  ((Finset.range l.length).filter fun i =>
    i + k ≤ l.length ∧ (∀ j < k, l.getD (i + j) 0 = m) ∧
    (i = 0 ∨ l.getD (i - 1) 0 ≠ m) ∧ (i + k = l.length ∨ l.getD (i + k) 0 ≠ m)).card

/-- R(n,m,k): the number of runs of `k` `m`'s in all compositions of `n`. -/
def R (n m k : ℕ) : ℕ :=
  ∑ c : Composition n, runCount c.blocks m k

/-- A045623(n): the number of 1's in all compositions of n+1; extended by 0 to negative `n`. -/
def A045623 (n : ℤ) : ℤ :=
  if n < 0 then 0 else ∑ c : Composition (n.toNat + 1), (c.blocks.count 1 : ℤ)

/-- A045891: first differences of A045623 (with A045623 = 0 at negative indices). -/
def A045891 (n : ℤ) : ℤ := A045623 n - A045623 (n - 1)

/-- A034007 (offset 0): first differences of A045891. -/
def a (n : ℕ) : ℤ := A045891 n - A045891 ((n : ℤ) - 1)

/-- Simay's conjectures 1 and 2 on runs of equal parts in compositions. -/
theorem main :
    (∀ n k : ℕ, 1 ≤ n → 1 ≤ k → (R (n + k - 1) 1 k : ℤ) = a (n - 1)) ∧
    (∀ n m k : ℕ, 1 ≤ m → 1 ≤ k →
      (R n m k : ℤ) = A045623 ((n : ℤ) - m * k) - 2 * A045623 ((n : ℤ) - m * (k + 1)) +
        A045623 ((n : ℤ) - m * (k + 2))) := by
  sorry

end OMA.S_oeis_a034007
