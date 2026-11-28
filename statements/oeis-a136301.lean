import Mathlib

/-!
# A136301: Frequency of occurrence for each possible "probability of derangement" for a Secret Santa drawing in which each person draws a name in sequence and the only person who does not draw someone else's name is the one who draws the final name.

Source: https://oeis.org/A136301
Credit: @Solfanbtc

Claim (entry formula, Peter Luschny, Apr 2024; also stated in A371761): with the table laid out
as in the Example section, row 2^n is row n + 1 of A371761.

The table. Column j ≥ 1 is the case of p = j + 2 people, numbered 1..p in drawing order; it has
2^(j-1) rows. The drawings counted are those where person p is forced to draw their own name,
i.e. permutations σ (person i draws name σ(i)) with σ(p) = p and σ(i) ≠ i for i < p:
derangements of the first j + 1 people. Each drawing has a pattern of bits, bit i being 1 when
name i was already drawn before person i's turn (σ⁻¹(i) < i). Bits 1, p-1 and p are forced; rows
are indexed by the middle bits i = 2..p-2, read as a binary number with person 2 most
significant, so row r holds the drawings whose middle bits encode r - 1. The entry is the number
of such drawings. (Example, p = 5: patterns 0-00-10, 0-01-10, 0-10-10, 0-11-10 occur 1, 5, 2, 1
times.) A python enumeration with exactly these conventions reproduces all 75 listed terms
(columns 1..6 in full and the first 12 rows of column 7).

Alignment with A371761 (from the entry's Mathematica snippet): row 2^n, read along columns
j = n, n+1, n+2, ..., is row n+1 of A371761, i.e. H(2^n, n + k) = A371761(n+1, k) for k ≥ 0.
Column j = n has only 2^(n-1) rows and contributes the value 0 = A371761(n+1, 0) by convention
(for n = 0 there is no column 0), so the claim is stated for k ≥ 1, where every entry exists.
A371761 is taken from its formula A(n,k) = Σ_{i=0..min(n,k)} (i!)^2 S2(n,i) S2(k,i)
(Stirling numbers of the second kind), which reproduces its data. Python check: the claim holds
for all n + k ≤ 9.
-/

namespace OMA.S_oeis_a136301

/-- Row code of a drawing among `j + 1` people (0-indexed names `t`): the middle bits, for
`t = 1..j-1` (people 2..j = p-2 in 1-indexed form), with bit weight `2^(j-1-t)`. -/
def code (j : ℕ) (σ : Equiv.Perm (Fin (j + 1))) : ℕ :=
  ∑ t : Fin (j + 1), if 1 ≤ t.val ∧ t.val ≤ j - 1 ∧ σ.symm t < t then 2 ^ (j - 1 - t.val) else 0

/-- A136301 as a table: `H r j`, row `r ≥ 1`, column `j ≥ 1` (zero when `r > 2^(j-1)`). -/
def H (r j : ℕ) : ℕ :=
  (Finset.univ.filter fun σ : Equiv.Perm (Fin (j + 1)) =>
    (∀ x, σ x ≠ x) ∧ code j σ + 1 = r).card

/-- A371761(n, k) = Σ_{i=0..min(n,k)} (i!)^2 S2(n,i) S2(k,i). -/
def A371761 (n k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (min n k + 1),
    i.factorial ^ 2 * Nat.stirlingSecond n i * Nat.stirlingSecond k i

theorem main : ∀ n k : ℕ, 1 ≤ k → H (2 ^ n) (n + k) = A371761 (n + 1) k := by
  sorry

end OMA.S_oeis_a136301
