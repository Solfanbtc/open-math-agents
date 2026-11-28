import Mathlib

/-!
# A083942: positions of the complete binary trees in A014486

Source: https://oeis.org/A083942 (see A014486, A002542, A000108, A014138)
Credit: @Solfanbtc

A014486 lists, in increasing order, the totally balanced binary numbers: those whose binary
expansion (most significant bit first) has as many 0's as 1's and in which, reading from the
left, the number of 0's never exceeds the number of 1's (`0` itself, the empty word, is the first
term): 0, 2, 10, 12, 42, 44, 50, 52, 56, ...
The complete binary tree of height `n` has `2^n - 1` internal nodes, and its breadth-first-wise
encoding (A002542) is the word `1^(2^n - 1) 0^(2^n - 1)`, i.e. the number
`v(n) = 2^(2^n - 1) · (2^(2^n - 1) - 1)`: 0, 2, 56, 16256, 1073709056, ... (the listed terms of
A002542). A083942(n) is the position (counted from 0) of `v(n)` in A014486: 0, 1, 8, 625, ...

Conjecture (Alexander Adamchuk, Nov 10 2007): `a(n) = ∑_{k=1..2^n-1} A000108(k)` (Catalan numbers),
equivalently `a(n) = A014138(2^n - 2)` for `n > 0`. We state the first form for all `n ≥ 0` (for
`n = 0` both sides are 0): the term of A014486 at position `∑_{k=1}^{2^n-1} C_k` is `v(n)`
(positions in A014486 are unique, since it is strictly increasing). Luschny's hypergeometric
reformulation is not included.

Sanity check (python): the predicate gives the listed terms of A014486, `v(n)` gives the listed
terms of A002542, and the positions of `v(0), ..., v(3)` are 0, 1, 8, 625 = the Catalan partial
sums.
-/

namespace OMA.S_oeis_a083942

/-- `m` is totally balanced (a term of A014486). -/
def IsTotallyBalanced (m : ℕ) : Prop :=
  let b := (Nat.digits 2 m).reverse
  b.count 0 = b.count 1 ∧ ∀ i, (b.take i).count 0 ≤ (b.take i).count 1

/-- The breadth-first encoding `1^(2^n - 1) 0^(2^n - 1)` of the complete binary tree of
height `n`. -/
def v (n : ℕ) : ℕ := 2 ^ (2 ^ n - 1) * (2 ^ (2 ^ n - 1) - 1)

/-- Adamchuk's conjecture: `A014486(∑_{k=1}^{2^n-1} C_k) = v(n)`, i.e.
`A083942(n) = ∑_{k=1}^{2^n-1} C_k`. -/
theorem main : ∀ n : ℕ,
    Nat.nth IsTotallyBalanced (∑ k ∈ Finset.Icc 1 (2 ^ n - 1), catalan k) = v n := by
  sorry

end OMA.S_oeis_a083942
