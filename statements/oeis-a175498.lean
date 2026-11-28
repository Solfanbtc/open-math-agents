import Mathlib

/-!
# A175498: greedy permutation with distinct adjacent differences

Source: https://oeis.org/A175498
Credit: @Solfanbtc

`a(1) = 1`; `a(n)` is the smallest positive integer not occurring earlier such that
`a(n) - a(n-1)` differs from every `a(k) - a(k-1)`, `2 ≤ k ≤ n - 1` (signed differences):
`1, 2, 4, 3, 6, 10, 5, 11, 7, 12, 9, 16, ...`.

Conjecture (Joerg Arndt, 2012): the lexicographically earliest permutation of `{1, 2, ..., n}` for
which the differences of adjacent numbers are all distinct (cf. A131529, which counts these
permutations with signed differences) has, as `n → ∞`, this sequence as its prefix. We state:
for every `m`, for all large enough `n`, the lexicographically earliest such permutation of
`{1, ..., n}` begins with `a(1), ..., a(m)`.

Definitions. A list `l` is valid for `n` if it is a permutation of `[1, ..., n]` and its signed
adjacent differences `l[i+1] - l[i]` are pairwise distinct; such lists exist for every `n`
(e.g. `1, n, 2, n-1, ...`), and the lexicographically earliest one is the valid `l` with no valid
`l' < l` (`<` is the lexicographic order on lists). In `next`, the search range `[0, 2M + 3)`,
`M` the largest term so far, always contains a candidate: `2M + 2` is new, and its difference to
the last term exceeds `M`, larger than every earlier difference.

Checks (python3, line-by-line mirror of `next`): the first 82 terms equal the OEIS data. Brute
force of the lexicographically earliest valid permutations for `n ≤ 28`: they share with `a` a
prefix of length 1, 2, 1, 4, 1, 2, 2, 3, 3, 4, 3, 4, 4, 7, 5, 7, 7, 8, 7, 8, 8, 9, 9, 9, 9, 10, 10,
10 (e.g. `n = 3` gives `1, 3, 2`), growing as the conjecture predicts.
-/

namespace OMA.S_oeis_a175498

/-- Signed differences of adjacent entries: `l[i+1] - l[i]`. -/
def diffs (l : List ℕ) : List ℤ := List.zipWith (fun x y => (y : ℤ) - x) l l.tail

/-- The greedy next term after the list `l` of terms so far. -/
def next (l : List ℕ) : ℕ :=
  ((List.range (2 * l.foldr max 0 + 3)).find? fun m =>
    decide (0 < m ∧ m ∉ l ∧ ((m : ℤ) - (l.getLast?.getD 0)) ∉ diffs l)).getD 0

/-- `pre n = [a(1), ..., a(n+1)]`. -/
def pre : ℕ → List ℕ
  | 0 => [1]
  | n + 1 => pre n ++ [next (pre n)]

/-- `A175498(n)` for `n ≥ 1`. -/
def a (n : ℕ) : ℕ := (pre n).getD (n - 1) 0

/-- `l` is a permutation of `{1, ..., n}` whose adjacent (signed) differences are distinct. -/
def Valid (n : ℕ) (l : List ℕ) : Prop := l.Perm (List.range' 1 n) ∧ (diffs l).Nodup

/-- `l` is the lexicographically earliest valid permutation of `{1, ..., n}`. -/
def IsLexEarliest (n : ℕ) (l : List ℕ) : Prop := Valid n l ∧ ∀ l', Valid n l' → ¬ l' < l

/-- For every `m`, the lexicographically earliest valid permutation of `{1, ..., n}` begins with
`a(1), ..., a(m)` for all sufficiently large `n`. -/
theorem main : ∀ m : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∀ l : List ℕ, IsLexEarliest n l →
    l.take m = (List.range m).map fun i => a (i + 1) := by
  sorry

end OMA.S_oeis_a175498
