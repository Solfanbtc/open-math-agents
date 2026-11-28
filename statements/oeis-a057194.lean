import Mathlib

/-!
# A057194: a(1) = 1; a(n+1) = (Product_{k=1..n} a(k)) * Sum_{k=1..n} a(k).

Source: https://oeis.org/A057194
Credit: @Solfanbtc

Conjecture (Jon Perry, Sep 12 2012, in the entry): a(n) < A216151(n) for all n > 1, where
A216151 is defined by the same rule a(n+1) = (Product_{k=1..n} a(k)) * Sum_{k=1..n} a(k) but
with a(1) = 1, a(2) = 2.

Conventions.
* `ext L` appends (product of L) * (sum of L) to the list L. The first n terms of A057194 are
  `ext^[n-1] [1]` and the first n terms of A216151 (n ≥ 2) are `ext^[n-2] [1, 2]`; the n-th term
  is the last element. This gives 1, 1, 2, 8, 192, 626688, ... and 1, 2, 6, 108, 151632, ...
  (the data of both entries).
-/

namespace OMA.S_oeis_a057194

/-- Append (product) * (sum). -/
def ext (L : List ℕ) : List ℕ := L ++ [L.prod * L.sum]

/-- A057194(n), n ≥ 1. -/
def a (n : ℕ) : ℕ := (ext^[n - 1] [1]).getLastD 0

/-- A216151(n), n ≥ 2. -/
def b (n : ℕ) : ℕ := (ext^[n - 2] [1, 2]).getLastD 0

theorem main : ∀ n : ℕ, 1 < n → a n < b n := by
  sorry

end OMA.S_oeis_a057194
