import Mathlib

/-!
# A036820: Number of partitions satisfying (cn(2,5) = cn(3,5) = 0).

Source: https://oeis.org/A036820
Credit: @Solfanbtc

`a(n)` (offset 0) is the number of partitions of `n` with no part `≡ 2` or `≡ 3 (mod 5)`:
`1, 1, 1, 1, 2, 3, 4, 4, 5, 7, 10, ...`.

Conjecture (Omar E. Pol, Oct 08 2011, in the entry): this sequence is related to the generalized
heptagonal numbers A085787 in the same way as the partition numbers A000041 are related to the
generalized pentagonal numbers A001318 (Euler's pentagonal number theorem), via the table in
A195825 (this sequence would be its column 3). The precise relation, as computed by the entry's
GW-BASIC program (Pol, Jun 10 2012), is the Euler-type recurrence
`a(n) = ∑_{j ≥ 1} A057077(j-1) · a(n - A085787(j))` for `n ≥ 1` (terms with `A085787(j) ≤ n`),
where `A085787(j)` (`j ≥ 1`) are the positive generalized heptagonal numbers
`1, 4, 7, 13, 18, 27, ...` and `A057077 = 1, 1, -1, -1, 1, 1, -1, -1, ...`. This recurrence is
the statement. (The other formulations in the comment, via the triangle A195837, are not stated.)

A python3 check: the partition count reproduces the data and the recurrence holds for all
`1 ≤ n < 400`.

Conventions:
* `A085787(j) = j(j+1)/2 + ⌊j/2⌋(⌊j/2⌋+1)/2` (the entry's formula `A000217(j) + A000217(⌊j/2⌋)`);
  since `A085787(j) ≥ j`, the sum may run over `1 ≤ j ≤ n`.
* `A057077(i) = 1` if `i mod 4 ∈ {0, 1}`, else `-1`.
-/

namespace OMA.S_oeis_a036820

/-- `a n = A036820(n)`: partitions of `n` with no part `≡ 2, 3 (mod 5)`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun p : n.Partition => ∀ i ∈ p.parts, i % 5 ≠ 2 ∧ i % 5 ≠ 3)).card

/-- Generalized heptagonal numbers `A085787(j)`. -/
def hept (j : ℕ) : ℕ := j * (j + 1) / 2 + (j / 2) * (j / 2 + 1) / 2

/-- `A057077(i)`: the periodic sequence `1, 1, -1, -1`. -/
def sgn (i : ℕ) : ℤ := if i % 4 = 0 ∨ i % 4 = 1 then 1 else -1

/-- Pol's conjecture: the Euler-type recurrence with generalized heptagonal numbers. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    (a n : ℤ) = ∑ j ∈ Finset.Icc 1 n,
      (if hept j ≤ n then sgn (j - 1) * (a (n - hept j) : ℤ) else 0) := by
  sorry

end OMA.S_oeis_a036820
