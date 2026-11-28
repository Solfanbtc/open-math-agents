import Mathlib

/-!
# A001277: Number of permutations of length n by rises.

Source: https://oeis.org/A001277
Credit: @Solfanbtc

Two conjectures of R. J. Mathar recorded in the entry (offset 2, so n >= 2):
1. (Jun 27 2022) a(n) = A177265(n) if n is even, and a(n) = A177265(n) - 1 if n is odd.
2. (Jul 01 2022) a(n) - n a(n-1) + (n-1) a(n-3) = 0, stated for n >= 5 so that all three
   indices are in the range n >= 2 of the sequence.

Definitions (from the names and cross-references of the entries):
* a(n) = A136123(n, 1) (Deutsch and Jovovic, in the entry): the number of permutations of
  {1, ..., n} having exactly one maximal string of increasing consecutive integers, i.e. exactly
  one maximal run of consecutive positions i, i+1, ..., i+r (r >= 1) carrying the values
  v, v+1, ..., v+r. With positions 0, ..., n-1, a succession is a position i with i + 1 < n and
  σ(i+1) = σ(i) + 1; the strings correspond to the maximal runs of successions, counted by their
  first position.
* A177265(n): the number of permutations of {1, ..., n} having exactly one string of consecutive
  fixed points (including singletons), i.e. the fixed points form exactly one maximal interval
  of consecutive integers; counted by its first point.
Both are computed here on `Equiv.Perm (Fin n)`, positions and values shifted to 0, ..., n-1.
Checked by brute force for n <= 9: the definitions give 1, 3, 12, 56, 321, 2175, 17008, 150504
(A001277) and 1, 1, 4, 12, 57, 321, 2176, 17008, 150505 (A177265), and both conjectures hold.
-/

namespace OMA.S_oeis_a001277

/-- The value at position `i` of a permutation of `Fin n`, as a natural number (0 outside). -/
def val {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : ℕ) : ℕ :=
  if h : i < n then (σ ⟨i, h⟩ : ℕ) else 0

/-- Position `i` is a succession: `σ(i+1) = σ(i) + 1`. -/
def IsSucc {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : ℕ) : Prop :=
  i + 1 < n ∧ val σ (i + 1) = val σ i + 1

instance {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : ℕ) : Decidable (IsSucc σ i) := by
  unfold IsSucc; infer_instance

/-- Position `i` is a fixed point. -/
def IsFix {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : ℕ) : Prop :=
  i < n ∧ val σ i = i

instance {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : ℕ) : Decidable (IsFix σ i) := by
  unfold IsFix; infer_instance

/-- Number of maximal strings of increasing consecutive integers of `σ`. -/
def numStrings {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  ((Finset.range n).filter fun i => IsSucc σ i ∧ (i = 0 ∨ ¬ IsSucc σ (i - 1))).card

/-- Number of maximal strings of consecutive fixed points of `σ`. -/
def numFixStrings {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  ((Finset.range n).filter fun i => IsFix σ i ∧ (i = 0 ∨ ¬ IsFix σ (i - 1))).card

/-- A001277(n) = A136123(n, 1). -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => numStrings σ = 1).card

/-- A177265(n). -/
def A177265 (n : ℕ) : ℕ :=
  (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => numFixStrings σ = 1).card

theorem main :
    (∀ n : ℕ, 2 ≤ n → (Even n → a n = A177265 n) ∧ (Odd n → a n = A177265 n - 1)) ∧
    (∀ n : ℕ, 5 ≤ n → (a n : ℤ) - n * a (n - 1) + (n - 1) * a (n - 3) = 0) := by
  sorry

end OMA.S_oeis_a001277
