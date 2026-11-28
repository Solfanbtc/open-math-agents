import Mathlib

/-!
# A066450: a(n) is the conjectured value of the minimal number to which repeated application of the "reverse and add!" algorithm in base n does not terminate in a palindrome.

Source: https://oeis.org/A066450
Credit: @Solfanbtc

Conjectures and open questions recorded in the entry:
1. "All the terms in this sequence except the first are only conjectures": each listed a(n)
   (n = 2..47, %S, %T, %U) is the least number whose reverse-and-add iteration in base n never
   reaches a palindrome. (a(2) = 22 is proved, Brockhaus; a(10) = 196 is open.)
2. "Is the sequence always positive?": in every base n ≥ 2 there is such a number (so that
   a(n) ≠ -1), stated in the affirmative form.
3. "For infinitely many n, a(n) = n^2 - n - 1."
4. "a(n) shows the same asymptotic behavior as n^2", read as a(n) ~ n^2 (a(n)/n^2 → 1), the
   reading consistent with 3.
`main` is the conjunction of 1-4.

Conventions:
* In base b, `rev` reverses the base-b digits; one step is x ↦ x + rev(x); x is a palindrome if
  its base-b digit list equals its reverse. r is a Lychrel number in base b if no iterate
  stepᵏ(r), k ≥ 0, is a palindrome (the start value counts, as in the upstream base-10
  `LychrelNumbers.IsLychrel10`). With this convention the minimum reproduces every listed term,
  whereas excluding k = 0 would give 100 instead of 103 in base 3. The entry's search starts at
  r = n, but all r < n are one-digit palindromes, so this is the least r overall.
* a(n) for 4 is `sInf {r | IsLychrel n r}` (meaningful by 2).
* Checked in Python with up to 1000 steps per start: the least non-palindromizing r reproduces
  all 46 listed terms; a(n) = n^2 - n - 1 for 22 of the listed bases (19, 20, 22, ..., 47).
-/

namespace OMA.S_oeis_a066450

open Filter Topology

/-- Digit reversal in base `b`. -/
def rev (b x : ℕ) : ℕ := Nat.ofDigits b (Nat.digits b x).reverse

/-- One reverse-and-add step in base `b`. -/
def step (b x : ℕ) : ℕ := x + rev b x

/-- `x` is a palindrome in base `b`. -/
def IsPal (b x : ℕ) : Prop := (Nat.digits b x).reverse = Nat.digits b x

/-- `r` is a Lychrel number in base `b`: no iterate (including `r`) is a palindrome. -/
def IsLychrel (b r : ℕ) : Prop := ∀ k : ℕ, ¬ IsPal b ((step b)^[k] r)

/-- The listed terms a(2), ..., a(47). -/
def terms : List ℕ :=
  [22, 103, 290, 708, 1079, 2656, 1021, 593, 196, 1011, 237, 2701, 361, 447, 413, 3297, 519, 341,
    379, 711, 461, 505, 551, 1022, 649, 701, 755, 811, 869, 929, 991, 1055, 1799, 1922, 1259, 1331,
    1405, 1481, 1559, 1639, 1595, 1762, 1891, 1934, 2069, 2161]

/-- A066450: the least Lychrel number in base `b`. -/
noncomputable def a (b : ℕ) : ℕ := sInf {r : ℕ | IsLychrel b r}

/-- The conjectures of A066450. -/
theorem main :
    (∀ i (hi : i < terms.length), IsLeast {r : ℕ | IsLychrel (i + 2) r} (terms.get ⟨i, hi⟩)) ∧
    (∀ b : ℕ, 2 ≤ b → ∃ r, IsLychrel b r) ∧
    {b : ℕ | 2 ≤ b ∧ IsLeast {r : ℕ | IsLychrel b r} (b ^ 2 - b - 1)}.Infinite ∧
    Tendsto (fun b : ℕ => (a b : ℝ) / (b : ℝ) ^ 2) atTop (𝓝 1) := by
  sorry

end OMA.S_oeis_a066450
