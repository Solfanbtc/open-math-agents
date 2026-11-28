import Mathlib

/-!
# A101513: a(1) = 1, a(2) = 2, a(3) = 3; triangle where n-th row has lowest n positive integers not yet in the sequence such that each integer has a prime divisor in common with at least one element of the (n-1)th row.

Source: https://oeis.org/A101513
Credit: @Solfanbtc

Row 1 is `1`, row 2 is `2, 3`, and for `n ≥ 3` row `n` consists of the `n` smallest positive
integers not in rows `1, ..., n-1` that share a prime factor with some element of row `n - 1`.
Rows: `1; 2, 3; 4, 6, 8; 9, 10, 12, 14; 5, 7, 15, 16, 18; ...`; `a` is the sequence read by rows
(offset 1).

Sloane's conjectures (Apr 22 2005, in the entry). A number is *postponed* if it cannot be placed
right away, i.e. it is coprime to the previous row; since rows are filled greedily in increasing
order, this means that some larger number occurs in the sequence before it (or it never occurs).
1. a number `n ≥ 4` is postponed iff `n` is prime;
2. every (positive) number appears (this also answers the entry's question: by construction no
   number is repeated, so `a` is then a permutation of the positive integers);
3. the primes appear in order;
4. `2p` (`p` prime) appears in one row and `p` in the next row;
5. with `c(i)` the `i`-th nonprime (A018252: 1, 4, 6, 8, 9, ...) and `k(3) = 4`,
   `n(n+1)/2 = π(⌊c(k(n-1))/2⌋) + k(n)` for `n ≥ 4`, the final term of row `n ≥ 3` is `c(k(n))`.

Minimal fix for 4: it fails for `p = 2, 3` (4 is in row 3 but 2 in row 2; 6 is in row 3 but 3 in
row 2: 2 and 3 are placed by the initial rows), so it is stated for primes `p ≥ 5`, matching the
range `n ≥ 4` of conjecture 1. In 5 the existence of `k` with values in `ℕ` is part of the claim
(the recurrence determines `k` uniquely).

python3, with the first 160 rows: the data is reproduced; every `n < 2000` appears; 1 and 3 hold
for `n < 2000`; 4 holds for primes `5 ≤ p < 1000`; 5 holds for `3 ≤ n < 60`
(`k = 4, 8, 11, 17, 22, 30, ...`, A104655).
-/

namespace OMA.S_oeis_a101513

/-- The next row after the rows `rs` (whose last row is `prev`): the `r = prev.length + 1`
smallest unused positive integers sharing a factor with an element of `prev`. Among the first
`used + r + 1` multiples of `prev.max` at least `r` are unused, so the search bound suffices. -/
def nextRow (rs : List (List ℕ)) : List ℕ :=
  let prev := rs.getLastD []
  let used := rs.flatten
  let r := prev.length + 1
  let B := prev.foldr max 0 * (used.length + r + 1)
  ((List.range (B + 1)).filter
    (fun x => 0 < x && !used.contains x && prev.any (fun z => 1 < Nat.gcd x z))).take r

/-- The rows `1, ..., m + 2` of the triangle. -/
def rowsUpTo : ℕ → List (List ℕ)
  | 0 => [[1], [2, 3]]
  | m + 1 => let rs := rowsUpTo m; rs ++ [nextRow rs]

/-- Row `n` of the triangle (`n ≥ 1`). -/
def row (n : ℕ) : List ℕ := (rowsUpTo n).getD (n - 1) []

/-- `a i`, the `i`-th term (`i ≥ 1`) of the sequence read by rows. -/
def a (i : ℕ) : ℕ := (rowsUpTo i).flatten.getD (i - 1) 0

/-- `n` is postponed: some term larger than `n` occurs before `n` has occurred. -/
def Postponed (n : ℕ) : Prop :=
  ∃ i : ℕ, 1 ≤ i ∧ n < a i ∧ ∀ j : ℕ, 1 ≤ j → j ≤ i → a j ≠ n

/-- The `i`-th nonprime positive integer, `i ≥ 1` (A018252). -/
noncomputable def c (i : ℕ) : ℕ := Nat.nth (fun m => 0 < m ∧ ¬ m.Prime) (i - 1)

theorem main :
    (∀ n : ℕ, 4 ≤ n → (Postponed n ↔ n.Prime)) ∧
    (∀ n : ℕ, 1 ≤ n → ∃ i : ℕ, 1 ≤ i ∧ a i = n) ∧
    (∀ p q i j : ℕ, p.Prime → q.Prime → p < q → 1 ≤ i → 1 ≤ j → a i = p → a j = q → i < j) ∧
    (∀ p : ℕ, p.Prime → 5 ≤ p → ∃ r : ℕ, 1 ≤ r ∧ 2 * p ∈ row r ∧ p ∈ row (r + 1)) ∧
    (∃ k : ℕ → ℕ, k 3 = 4 ∧
      (∀ n : ℕ, 4 ≤ n → n * (n + 1) / 2 = Nat.primeCounting (c (k (n - 1)) / 2) + k n) ∧
      ∀ n : ℕ, 3 ≤ n → (row n).getLast? = some (c (k n))) := by
  sorry

end OMA.S_oeis_a101513
