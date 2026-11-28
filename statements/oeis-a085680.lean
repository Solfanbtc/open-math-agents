import Mathlib

/-!
# A085680: Size of largest code of length n and constant weight 2 that can correct a single adjacent transposition.

Source: https://oeis.org/A085680
Credit: @Solfanbtc

For `n ≥ 2`, form the graph whose vertices are the binary vectors of length `n` with exactly two
1's, two vertices being adjacent when one is obtained from the other by transposing a pair of
adjacent coordinates. `a(n)` is the maximal size of a set `S` of vertices such that the distance
between every pair of distinct vertices of `S` is at least 3 (a 2-packing of the 2-token graph
of the path `P_n`). Data (`n ≥ 2`): `1, 1, 2, 3, 4, 6, 7, 9, 11, 13, ...`.

Conjecture (Luis Manuel Rivera and colleagues, Mar 23 2017, in the entry): for `n ≥ 10`,
`a(n) = (n^2 - n + 20)/10` if `n ≡ 0, 1 (mod 5)`, `(n^2 - n + 18)/10` if `n ≡ 2, 4 (mod 5)`,
`(n^2 - n + 14)/10` if `n ≡ 3 (mod 5)` (they proved these as lower bounds).
(Rob Pratt's conjecture in the entry, that the second differences are eventually periodic
`1, 0, 0, 0, 0`, is a consequence of this one, so it is not stated separately.)

A python3 check: the three formulas are integers and equal the 41 known values `a(10..50)`;
a brute-force search reproduces `a(2..8)`.

Conventions: a vertex is a 2-element subset `u ⊆ {0, ..., n-1}` (the positions of the 1's);
`u` and `v` are adjacent iff their symmetric difference is `{i, i+1}` with `i + 1 < n`
(exactly an adjacent transposition moving one 1). Distance at least 3 between distinct `u, v`
means: not adjacent and no common neighbour. The division is exact.
-/

namespace OMA.S_oeis_a085680

/-- The vertices: 2-element subsets of `{0, ..., n-1}`. -/
def vertices (n : ℕ) : Finset (Finset ℕ) := (Finset.range n).powersetCard 2

/-- Adjacency: `v` is obtained from `u` by an adjacent transposition. -/
def Adj (n : ℕ) (u v : Finset ℕ) : Prop := ∃ i, i + 1 < n ∧ symmDiff u v = {i, i + 1}

/-- `S` is a code: distinct codewords are at distance at least 3. -/
def IsCode (n : ℕ) (S : Finset (Finset ℕ)) : Prop :=
  S ⊆ vertices n ∧ ∀ u ∈ S, ∀ v ∈ S, u ≠ v →
    ¬ Adj n u v ∧ ¬ ∃ w ∈ vertices n, Adj n u w ∧ Adj n w v

/-- Rivera et al.'s conjectured value of `a(n)` for `n ≥ 10`. -/
def formula (n : ℕ) : ℕ :=
  if n % 5 = 0 ∨ n % 5 = 1 then (n ^ 2 - n + 20) / 10
  else if n % 5 = 3 then (n ^ 2 - n + 14) / 10
  else (n ^ 2 - n + 18) / 10

/-- The conjecture: for `n ≥ 10`, the largest code has size `formula n`. -/
theorem main : ∀ n : ℕ, 10 ≤ n →
    IsGreatest {k : ℕ | ∃ S : Finset (Finset ℕ), IsCode n S ∧ S.card = k} (formula n) := by
  sorry

end OMA.S_oeis_a085680
