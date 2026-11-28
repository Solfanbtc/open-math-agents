import Mathlib

/-!
# A082184: The a(n)-th triangular number is the sum of the n-th triangular number and the smallest triangular number possible.

Source: https://oeis.org/A082184
Credit: @Solfanbtc

`T(i) = i(i+1)/2`. For `n ≥ 2` (the offset), A082183(n) is the least `k > 0` such that
`T(n) + T(k)` is triangular, and `a(n)` is the `m` with `T(m) = T(n) + T(k)` for that `k`.
Since `T(n) + T(k)` increases with `k`, `a(n)` is also the least `m` such that
`T(m) = T(n) + T(k)` for some `k > 0` (the entry's Maple program searches `m` upwards).
Such `k` exists for `n ≥ 2` (`k = T(n) - 1`, `m = T(n)`). This reproduces every term of
%S, %T, %U (Python).

A068194: the `k` for which the only way to write `T(k)` as a sum of two or more consecutive
positive integers is `1 + 2 + … + k`. A068195: the numbers `T(k)` for such `k`.

Conjecture (Ralf Stephan, in the entry): "partial maxima of sequence are at index i with value
from A068195 and also a(i) - A082183(i) = 1, where i is in A068194". Read as: for `i ≥ 2`,
`a(i)` is a partial maximum (record: larger than every earlier term) iff `i` is in A068194,
every record value is in A068195, and `a(i) - A082183(i) = 1` for every `i ≥ 2` in A068194.

Status: false as stated. The last part holds (for such `i` the only factorization of `i(i+1)`
into opposite-parity factors is the trivial one, giving `k = T(i) - 1`, `m = T(i)`; see
R. Schroeppel's comment in A082183). But Python, using the entry's own search, gives
`a(2143) = 34321`, larger than every earlier term (the previous record is `a(256) = 32896`).
`2143` is not in A068194 (`2143` is prime but not Mersenne, and `2144` is not a Fermat prime),
and `34321` is not triangular. The records up to `2·10^5` are at
`2, 3, 4, 7, 16, 31, 127, 256, 2143, 2272, 2656, 2752, 3391, 4288, 4672, 6976, 8191, 65536,
131071`. So the negation of the statement below is provable by a finite computation.
-/

namespace OMA.S_oeis_a082184

/-- The `i`-th triangular number. -/
def T (i : ℕ) : ℕ := i * (i + 1) / 2

/-- A082184. -/
noncomputable def a (n : ℕ) : ℕ := sInf {m : ℕ | ∃ k : ℕ, 0 < k ∧ T n + T k = T m}

/-- A082183. -/
noncomputable def k (n : ℕ) : ℕ := sInf {k : ℕ | 0 < k ∧ ∃ m : ℕ, T n + T k = T m}

/-- `i` is in A068194. -/
def InA068194 (i : ℕ) : Prop :=
  ∀ r j : ℕ, 2 ≤ r → 1 ≤ j → ∑ t ∈ Finset.range r, (j + t) = T i → j = 1 ∧ r = i

/-- `x` is in A068195. -/
def InA068195 (x : ℕ) : Prop := ∃ i : ℕ, InA068194 i ∧ x = T i

/-- `a(i)` is a partial maximum of A082184 (offset 2). -/
def IsRecord (i : ℕ) : Prop := 2 ≤ i ∧ ∀ j : ℕ, 2 ≤ j → j < i → a j < a i

theorem main :
    (∀ i : ℕ, 2 ≤ i → (IsRecord i ↔ InA068194 i)) ∧
    (∀ i : ℕ, IsRecord i → InA068195 (a i)) ∧
    (∀ i : ℕ, 2 ≤ i → InA068194 i → a i - k i = 1) := by
  sorry

end OMA.S_oeis_a082184
