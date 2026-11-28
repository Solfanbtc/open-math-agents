import Mathlib

/-!
# A270264: The cumulative sum of the digits of successive terms reproduces the prime number sequence; this is the lexicographically earliest sequence with this property.

Source: https://oeis.org/A270264
Credit: @Solfanbtc

Conjecture (N. J. A. Sloane and Chai Wah Wu, Mar 15 2016, in the entry): the sequence is equal
to {1} union A054683 (numbers whose sum of digits is even); Wu notes this is equivalent to
Polignac's conjecture, still open.

Conventions.
* The defining property: the sum of the decimal digits of a(1), ..., a(n) is the n-th prime,
  i.e. digitsum(a(n)) = p(n) - p(n-1) (with p(0) := 0). As the data show (a(3) = 11, not 2), the
  terms are distinct positive integers, so the lexicographically earliest such sequence is the
  greedy one: a(n) is the least positive integer, not among a(1), ..., a(n-1), whose digit sum
  is p(n) - p(n-1) (such integers always exist, so each greedy choice never blocks a later one).
  Checked with python3: this reproduces all 88 listed terms.
* "Equal to {1} union A054683" is read as equality of sets (the entry says "a permutation of";
  the terms are distinct by construction). A054683 starts with 0, which can never be a term
  (every term has positive digit sum p(n) - p(n-1) ≥ 1), so the minimal fix is to take the
  positive members of A054683: the claim is that the set of terms is
  {1} ∪ {n ≥ 1 : the digit sum of n is even}.
* Indexing here is 0-based: `a k` is a(k+1), with digit sum `nth Prime k - nth Prime (k-1)`
  (and `nth Prime 0 = 2` for `k = 0`).
-/

namespace OMA.S_oeis_a270264

/-- Sum of the decimal digits. -/
def digitSum (m : ℕ) : ℕ := (Nat.digits 10 m).sum

/-- The required digit sum of the term of index `k` (0-based): `p(k+1) - p(k)`, `p(0) = 0`. -/
noncomputable def gap (k : ℕ) : ℕ :=
  Nat.nth Nat.Prime k - (if k = 0 then 0 else Nat.nth Nat.Prime (k - 1))

/-- The first `k` terms, chosen greedily. -/
noncomputable def terms : ℕ → List ℕ
  | 0 => []
  | k + 1 =>
    let L := terms k
    L ++ [sInf {m : ℕ | 1 ≤ m ∧ m ∉ L ∧ digitSum m = gap k}]

/-- A270264, 0-indexed: `a k` is the (k+1)-th term. -/
noncomputable def a (k : ℕ) : ℕ := (terms (k + 1)).getD k 0

theorem main : Set.range a = {1} ∪ {n : ℕ | 1 ≤ n ∧ Even (digitSum n)} := by
  sorry

end OMA.S_oeis_a270264
