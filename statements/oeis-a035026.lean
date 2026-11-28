import Mathlib

/-!
# A035026: Number of times that i and 2n-i are both prime, for i = 1, ..., 2n-1.

Source: https://oeis.org/A035026
Credit: @Solfanbtc

Conjectures (Robert G. Wilson v, OEIS A035026, comments, Dec 15 2016), for the values
k = 0, 1, 2, ... in order:
1. "Conjectured last occurrence of k: 1, 3, 6, 19, 34, 31, 64, 61, 76, 79, 94, 83, 166, 199,
   136, 181, 184, 229, 244, 271, 316, 277, 346, 313, 301, 293, ...": for each listed k, the
   value k is taken at the listed index and never at a larger index.
2. "Conjectured number occurrences of k: 1, 2, 2, 3, 6, 3, 8, 4, 7, 5, 11, 5, 11, 8, 10, 3,
   17, 7, 16, 3, 13, 8, 21, 4, 12, 3, 22, 7, 20, 8, 15, ...": for each listed k, the set of
   indices n ≥ 1 with a(n) = k is finite with exactly the listed number of elements.
`main` is the conjunction of 1 and 2 for every listed term (k < 26, resp. k < 31). The part
k = 0 of 1 is Goldbach's conjecture (a(n) ≥ 1 for n ≥ 2), so this is a strengthening of it.

Conventions:
* Offset 1: a(n) = #{i : 1 ≤ i ≤ 2n - 1, i and 2n - i prime}, so a(1) = 0, a(2) = 1, a(3) = 1.
  The first occurrences (1, 2, 4, 5, ...) show that the lists are indexed from k = 0.
* Checked in Python: `a` reproduces all listed terms of %S, %T, %U, and both lists hold for
  n ≤ 300000 (the minimum of a(n) over 2000 ≤ n ≤ 300000 is 85).
-/

namespace OMA.S_oeis_a035026

/-- A035026: the number of `i ∈ [1, 2n-1]` with `i` and `2n - i` both prime. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 (2 * n - 1)).filter fun i => i.Prime ∧ (2 * n - i).Prime).card

/-- The conjectured last occurrence of `k`, for `k = 0, ..., 25`. -/
def lastOcc : List ℕ :=
  [1, 3, 6, 19, 34, 31, 64, 61, 76, 79, 94, 83, 166, 199, 136, 181, 184, 229, 244, 271, 316,
    277, 346, 313, 301, 293]

/-- The conjectured number of occurrences of `k`, for `k = 0, ..., 30`. -/
def numOcc : List ℕ :=
  [1, 2, 2, 3, 6, 3, 8, 4, 7, 5, 11, 5, 11, 8, 10, 3, 17, 7, 16, 3, 13, 8, 21, 4, 12, 3, 22, 7,
    20, 8, 15]

/-- Wilson's conjectures on the last occurrence and the number of occurrences of each value. -/
theorem main :
    (∀ k (hk : k < lastOcc.length),
        a (lastOcc.get ⟨k, hk⟩) = k ∧ ∀ n, lastOcc.get ⟨k, hk⟩ < n → a n ≠ k) ∧
    (∀ k (hk : k < numOcc.length),
        {n : ℕ | 1 ≤ n ∧ a n = k}.Finite ∧
          {n : ℕ | 1 ≤ n ∧ a n = k}.ncard = numOcc.get ⟨k, hk⟩) := by
  sorry

end OMA.S_oeis_a035026
