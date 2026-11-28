import Mathlib

/-!
# A112310: block sums of the number of terms in lazy Fibonacci representations

Source: https://oeis.org/A112310 (with https://oeis.org/A023610)
`a(n)` (offset 0) is the number of terms in the lazy Fibonacci representation of `n`, i.e. the
number of ones in its maximal Fibonacci bit-representation (A104326): `n` is written as a sum of
distinct Fibonacci numbers `F(2) = 1, F(3) = 2, F(4) = 3, ...` such that, below the largest one
used, no two consecutive Fibonacci numbers are both missing (no `00` in the bit string).
Data: 0, 1, 1, 2, 2, 2, 3, 2, 3, 3, 3, 4, 3, 3, ...
Conjecture (Gary W. Adamson, Nov 02 2010): "if we split the sequence in groups that contain
Fibonacci(k) terms like (0), (1), (1, 2), (2, 2, 3), (2, 3, 3, 3, 4), (3, 3, 4, 3, 4, 4, 4, 5) etc,
the sums in the groups are the terms of A023610." A023610 (offset 0) is the convolution of the
Fibonacci numbers with `{F(2), F(3), F(4), ...}`: `∑_{k=0}^{m} F(k+1) F(m-k+2)` = 1, 3, 7, 15, 30, ...

Formalization. The groups have sizes `F(1), F(2), F(3), ... = 1, 1, 2, 3, 5, 8, ...`; group
`j ≥ 0` consists of the indices `F(j+2) - 1 ≤ n < F(j+3) - 1`. Their sums are 0, 1, 3, 7, 15, 30,
so the first group `(0)` (sum 0) precedes A023610, and the claim is: for every `j ≥ 1`, the sum
over group `j` is `A023610(j - 1)`.
`a n` is the size of a lazy representation of `n` using indices in `[2, n+2]` (enough, since
`F(n+3) > n`); the lazy representation exists and is unique, so the `sup` is just its size (an
`#eval` confirms exactly one such representation for `n ≤ 13`, and `a(0..13)` matches the data).
Checked with python3: the 105 listed terms, and the group sums for `j = 1..20`.

Credit: @Solfanbtc
-/

namespace OMA.S_oeis_a112310

/-- `S` (a set of Fibonacci indices `≥ 2`) is a lazy Fibonacci representation of `n`:
`∑_{i ∈ S} F(i) = n`, and no two consecutive indices below the largest one are both missing. -/
def IsLazyRep (n : ℕ) (S : Finset ℕ) : Prop :=
  (∀ i ∈ S, 2 ≤ i) ∧ ∑ i ∈ S, Nat.fib i = n ∧
    ∀ i ∈ Finset.Ico 2 (S.sup id), i ∈ S ∨ i + 1 ∈ S

instance (n : ℕ) : DecidablePred (IsLazyRep n) := fun S => by unfold IsLazyRep; infer_instance

/-- A112310: the number of terms in the lazy Fibonacci representation of `n`. -/
def a (n : ℕ) : ℕ :=
  (((Finset.Icc 2 (n + 2)).powerset.filter (IsLazyRep n)).image Finset.card).sup id

/-- A023610: the convolution of the Fibonacci numbers with `F(2), F(3), F(4), ...`. -/
def A023610 (m : ℕ) : ℕ := ∑ k ∈ Finset.range (m + 1), Nat.fib (k + 1) * Nat.fib (m - k + 2)

theorem main : ∀ j : ℕ, 1 ≤ j →
    ∑ n ∈ Finset.Ico (Nat.fib (j + 2) - 1) (Nat.fib (j + 3) - 1), a n = A023610 (j - 1) := by
  sorry

end OMA.S_oeis_a112310
