import Mathlib

/-!
# A057746: Even numbers not the sum of a pair of twin even-lucky-numbers.

Source: https://oeis.org/A057746
Credit: @Solfanbtc

The sequence lists 2, 292, 324, 356, 372, 612, 1074, 1202, 1842 and is "Conjectured to be
complete". Stated: an even number n ≥ 2 is not a sum x + y of two twin even-lucky numbers iff n
is one of these nine numbers.

Conventions.
* Even-lucky numbers (A045954): write the even numbers 2, 4, 6, 8, ...; the second term is 4,
  so remove every 4th number; the next surviving term (third) is 6, so remove every 6th of the
  survivors; and so on: at stage k (k = 1, 2, ..., 0-indexed position) take the current k-th
  term v and delete the terms at positions v, 2v, 3v, ... (1-indexed). Whether x survives only
  depends on the terms ≤ x, so `IsEvenLucky x` runs the sieve on the even numbers in [2, x]
  (enough stages: at most their number). python3: 2, 4, 6, 10, 12, 18, 20, 22, 26, ... (A045954).
* Twin even-lucky numbers (A045955 lower, A045956 upper members): even-lucky x such that x + 2
  or x - 2 is also even-lucky. "Sum of a pair" = x + y with x, y twin even-lucky numbers,
  x = y allowed: this is the reading that reproduces the data (python3, n < 20000: the
  non-representable even numbers are exactly the nine listed ones; forbidding x = y would add
  4, 196, 260, ...).
-/

namespace OMA.S_oeis_a057746

/-- Delete the terms at 1-indexed positions v, 2v, 3v, .... -/
def removeEvery (v : ℕ) (L : List ℕ) : List ℕ :=
  (L.zipIdx.filter fun p => (p.2 + 1) % v ≠ 0).map Prod.fst

/-- Run the sieve stages k, k+1, ... (with fuel). -/
def sieveAux : ℕ → ℕ → List ℕ → List ℕ
  | 0, _, L => L
  | fuel + 1, k, L => if k < L.length then sieveAux fuel (k + 1) (removeEvery (L.getD k 0) L) else L

/-- x is an even-lucky number (A045954). -/
def IsEvenLucky (x : ℕ) : Prop :=
  x ∈ sieveAux (x + 1) 1 ((List.range (x + 1)).filter fun y => 2 ≤ y ∧ y % 2 = 0)

/-- x is a member of a pair of twin even-lucky numbers (A045955 ∪ A045956). -/
def IsTwinEvenLucky (x : ℕ) : Prop :=
  IsEvenLucky x ∧ (IsEvenLucky (x + 2) ∨ (4 ≤ x ∧ IsEvenLucky (x - 2)))

/-- The listed terms of A057746. -/
def listed : Finset ℕ := {2, 292, 324, 356, 372, 612, 1074, 1202, 1842}

theorem main : ∀ n : ℕ, 2 ≤ n → Even n →
    ((¬ ∃ x y : ℕ, IsTwinEvenLucky x ∧ IsTwinEvenLucky y ∧ x + y = n) ↔ n ∈ listed) := by
  sorry

end OMA.S_oeis_a057746
