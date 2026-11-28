import Mathlib

/-!
# A065306: The Goldbach permutation: take A065305, cross out repetitions and subtract 2 from each term.

Source: https://oeis.org/A065306
Credit: @Solfanbtc

A065305 is the triangle `T(n, k) = (p_n + p_k) / 2` for `n ≥ k ≥ 2` (`p_n` the `n`-th prime), read
by rows (`n = 2, 3, ...`), each row with `k = 2, ..., n`: `3; 4, 5; 5, 6, 7; 7, 8, 9, 11; ...`.
A065306 keeps the first occurrence of each value, in order, and subtracts 2:
`1, 2, 3, 4, 5, 6, 7, 9, 8, 10, ...` (offset 1).

Claim (the entry): the sequence would be a permutation of the natural numbers (here the positive
integers `1, 2, 3, ...`, the values the sequence takes) if Goldbach's conjecture holds (every even
integer greater than two is the sum of two primes). Stated as `Goldbach → a is a bijection from its
index set onto {m | 1 ≤ m}`.

A python3 check: this construction reproduces the 72 data terms, and every `m < 1000` with
`m ≥ 3` occurs in A065305.

Conventions:
* 0-indexed: `a n = A065306(n + 1)`, `f i` is the `i`-th entry (0-indexed) of the flattened
  triangle; row `r ≥ 0` is `n = r + 2`, its entries are `k = j + 2` for `j ≤ r`.
* `p_n = Nat.nth Nat.Prime (n - 1)` (so `p_2 = 3`). All `T(n, k)` are integers since both primes
  are odd.
* Goldbach's conjecture: every even `n > 2` is a sum of two primes.
-/

namespace OMA.S_oeis_a065306

/-- The `n`-th prime, 1-indexed (`prime 1 = 2`). -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- Row `r` of A065305 (the row of `n = r + 2`): `(p_{r+2} + p_{j+2}) / 2` for `j = 0, ..., r`. -/
noncomputable def row (r : ℕ) : List ℕ :=
  (List.range (r + 1)).map fun j => (prime (r + 2) + prime (j + 2)) / 2

/-- The `i`-th entry (0-indexed) of A065305 read by rows (rows `0..i` hold at least `i + 1`
entries). -/
noncomputable def f (i : ℕ) : ℕ := ((List.range (i + 1)).flatMap row).getD i 0

/-- `i` is the position of the first occurrence of its value in A065305. -/
def IsFirst (i : ℕ) : Prop := ∀ j < i, f j ≠ f i

/-- `a n = A065306(n + 1)`: the `n`-th first-occurring value of A065305, minus 2. -/
noncomputable def a (n : ℕ) : ℕ := f (Nat.nth IsFirst n) - 2

/-- Goldbach's conjecture: every even `n > 2` is the sum of two primes. -/
def Goldbach : Prop := ∀ n : ℕ, 2 < n → Even n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n

/-- If Goldbach's conjecture holds, A065306 is a permutation of the positive integers. -/
theorem main : Goldbach → Set.BijOn a Set.univ {m | 1 ≤ m} := by
  sorry

end OMA.S_oeis_a065306
