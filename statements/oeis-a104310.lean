import Mathlib

/-!
# A104310: Maximum length of perfect rulers that can be made from segments not exceeding n.

Source: https://oeis.org/A104310
Credit: @Solfanbtc

Conjecture (Hugo Pfoertner, OEIS A104310, comment, 2005): a(8) = 81.
According to the entry (%E), this was proven via exhaustive search by Fabian Schwartau, Yannic
Schröder, Lars Wolf and Joerg Schoebel (Feb 23 2021), who also added a(9) = 103 and
a(10) = 135. It is stated here as the original conjecture.

Conventions (Luschny's "Perfect Rulers" nomenclature, as the entry says):
* A ruler of length `L` is a finset `S ⊆ {0, ..., L}` containing `0` and `L` (the marks). It is
  complete if every distance `d ≤ L` is the difference of two marks. It is perfect if it is
  complete and no complete ruler of length `L` has fewer marks (the minimum is A046693(L)).
* It is "made from segments not exceeding n" if consecutive marks are at distance `≤ n`: every
  mark `a < L` has a mark `b` with `a < b ≤ a + n`.
* a(n) is the largest such `L`; `IsGreatest` also asserts that the maximum exists.
* Checked in Python (exhaustive search, using the minimal mark counts A046693): this definition
  gives 2, 7, 18, 25, 37 for n = 1..5, agreeing with the rulers of the example. Its value 37
  for n = 5 agrees with the example ruler [0,1,2,3,8,13,18,23,28,33,37] (11 marks, the minimum
  for length 37) but not with the term 32 in %S, which looks like a typo in the data. It does
  not affect a(8).
-/

namespace OMA.S_oeis_a104310

/-- `S` is a complete ruler of length `L`. -/
def IsCompleteRuler (S : Finset ℕ) (L : ℕ) : Prop :=
  S ⊆ Finset.range (L + 1) ∧ 0 ∈ S ∧ L ∈ S ∧ ∀ d ≤ L, ∃ a ∈ S, ∃ b ∈ S, a + d = b

/-- `S` is a perfect ruler of length `L`: complete, with the fewest marks. -/
def IsPerfectRuler (S : Finset ℕ) (L : ℕ) : Prop :=
  IsCompleteRuler S L ∧ ∀ T : Finset ℕ, IsCompleteRuler T L → S.card ≤ T.card

/-- Consecutive marks of `S` (a ruler of length `L`) are at distance at most `n`. -/
def SegmentsAtMost (S : Finset ℕ) (L n : ℕ) : Prop :=
  ∀ a ∈ S, a < L → ∃ b ∈ S, a < b ∧ b ≤ a + n

/-- Lengths of perfect rulers made from segments not exceeding `n`. -/
def lengths (n : ℕ) : Set ℕ :=
  {L | ∃ S : Finset ℕ, IsPerfectRuler S L ∧ SegmentsAtMost S L n}

/-- Pfoertner's conjecture: `a(8) = 81`. -/
theorem main : IsGreatest (lengths 8) 81 := by
  sorry

end OMA.S_oeis_a104310
