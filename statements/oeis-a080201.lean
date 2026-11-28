import Mathlib

/-!
# A080201: Numbers that do not occur as differences between terms of the Mian-Chowla variant A051788.

Source: https://oeis.org/A080201
Credit: @Solfanbtc

A051788: `b(1) = 1`, `b(2) = 3`, and for `n > 2`, `b(n)` is the least value `> b(n-1)` such
that the pairwise differences `b(i) - b(j)` (`i > j`) of `b(1), …, b(n)` are all distinct.
(Python reproduces all 50 terms of the data of A051788.) `IsA051788 b` says that `b`
satisfies this recursion; it determines `b(n)` for every `n ≥ 1` by induction, so the statement
is about A051788 itself. The sequence is 1-indexed; `b 0` is irrelevant.

A080201 lists the positive integers that never occur as a difference `b(i) - b(j)`, `i > j`.
The entry says: "Terms are only conjectures. Elements might be eliminated by higher terms of
A051788, which was checked up to 4*10^6." The conjectured claim is that the data
`49, 50, 71, …, 188` are exactly the first 22 terms: a positive integer `d ≤ 188` is never
such a difference iff `d` is one of the 22 listed numbers. (Checked in Python with all 639 terms
of A051788 below `4·10^6`: the missing differences up to 188 are exactly the listed ones.)
-/

namespace OMA.S_oeis_a080201

/-- The differences `b i - b j`, `1 ≤ j < i ≤ n`, are pairwise distinct. -/
def DiffsDistinct (b : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ i j k l : ℕ, 1 ≤ j → j < i → i ≤ n → 1 ≤ l → l < k → k ≤ n →
    b i - b j = b k - b l → i = k ∧ j = l

/-- `b` is A051788: `b 1 = 1`, `b 2 = 3`, and each `b (n + 1)` (`n ≥ 2`) is the least number
greater than `b n` keeping all differences of `b 1, …, b (n + 1)` distinct. -/
def IsA051788 (b : ℕ → ℕ) : Prop :=
  b 1 = 1 ∧ b 2 = 3 ∧ ∀ n : ℕ, 2 ≤ n →
    IsLeast {m : ℕ | b n < m ∧ DiffsDistinct (Function.update b (n + 1) m) (n + 1)} (b (n + 1))

/-- The 22 listed terms of A080201. -/
def L : Finset ℕ :=
  {49, 50, 71, 72, 76, 82, 90, 93, 95, 96, 119, 128, 139, 143, 152, 162, 172, 173, 180, 182,
    185, 188}

theorem main : ∀ b : ℕ → ℕ, IsA051788 b → ∀ d : ℕ, 1 ≤ d → d ≤ 188 →
    ((¬ ∃ i j : ℕ, 1 ≤ j ∧ j < i ∧ b i - b j = d) ↔ d ∈ L) := by
  sorry

end OMA.S_oeis_a080201
