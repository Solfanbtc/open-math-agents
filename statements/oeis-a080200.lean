import Mathlib

/-!
# A080200: Numbers that do not occur as differences between terms of the Mian-Chowla sequence.

Source: https://oeis.org/A080200
Credit: @Solfanbtc

The entry: "Terms are only conjectures. Elements might be eliminated by higher terms of
A005282" (terms through a(50) confirmed against the first 100000 terms of A005282, Reichert
2026). The conjecture stated: the positive integers m ≤ 302 (the last listed term) that never
occur as a difference of two terms of the Mian-Chowla sequence are exactly the 50 listed terms
33, 88, 98, ..., 297, 302 (all terms of %S, %T, %U).

Conventions.
* Mian-Chowla sequence A005282 (offset 1): a(1) = 1, and a(n+1) is the least number > a(n)
  such that all pairwise sums a(i) + a(j), i ≤ j ≤ n+1, are distinct. `IsMianChowla` is the same
  defining property as in statements/oeis-a005282.lean; it determines a(n) for every n ≥ 1, and
  the statement is made for every such a.
* m "occurs as a difference" iff a(j) - a(i) = m for some 1 ≤ i < j.
* python3 check with the first 1000 terms: every m ≤ 302 not listed occurs except 216 (which
  needs later terms; Pfoertner/Reichert's longer checks confirm the list), and no listed m occurs.
-/

namespace OMA.S_oeis_a080200

/-- The terms `a 1, …, a n` have pairwise distinct sums `a i + a j` (`i ≤ j`). -/
def SumsDistinct (a : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ i j k l : ℕ, 1 ≤ i → i ≤ j → j ≤ n → 1 ≤ k → k ≤ l → l ≤ n →
    a i + a j = a k + a l → i = k ∧ j = l

/-- `a` is the Mian-Chowla sequence. -/
def IsMianChowla (a : ℕ → ℕ) : Prop :=
  a 1 = 1 ∧ ∀ n : ℕ, 1 ≤ n →
    IsLeast {m : ℕ | a n < m ∧ SumsDistinct (Function.update a (n + 1) m) (n + 1)} (a (n + 1))

/-- The listed terms of A080200. -/
def listed : Finset ℕ :=
  {33, 88, 98, 99, 105, 106, 112, 126, 130, 132, 134, 150, 152, 154, 156, 162, 163, 165, 170,
    176, 184, 188, 198, 205, 214, 215, 217, 220, 222, 228, 234, 235, 240, 246, 252, 255, 263,
    266, 267, 268, 274, 276, 279, 281, 287, 290, 291, 294, 297, 302}

theorem main : ∀ a : ℕ → ℕ, IsMianChowla a →
    ∀ m : ℕ, 1 ≤ m → m ≤ 302 →
      ((¬ ∃ i j : ℕ, 1 ≤ i ∧ i < j ∧ a j - a i = m) ↔ m ∈ listed) := by
  sorry

end OMA.S_oeis_a080200
