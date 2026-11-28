import Mathlib

/-!
# A072540: Numbers that are not differences between successive Ulam numbers (A002858).

Source: https://oeis.org/A072540
Credit: @Solfanbtc

The listed terms are `6, 11, 14, 16, 18, 21` (%S), and the entry says that the sequence is
conjectured to continue `23, 26, 28, 31, 33` (Jud McCranie, 2013; the list holds through the
first 28 billion Ulam numbers, 2016). Per N. J. A. Sloane's comment, all entries are conjectural:
no proof is known that any of them never occurs as a gap.

We state the conjecture with the same strength as the claimed initial segment: among the positive
integers `d ≤ 33`, `d` is never a difference `a(n+1) - a(n)` of successive Ulam numbers if and only
if `d ∈ {6, 11, 14, 16, 18, 21, 23, 26, 28, 31, 33}`. (`0` is excluded: the numbers in the sequence
are positive, and `0` is trivially never a gap.)

Conventions:
* The Ulam sequence (A002858) is characterized as in `Erdos342.IsUlamSequence` in
  formal-conjectures: `a 0 = 1`, `a 1 = 2`, and for `n ≥ 2`, `a n` is the least integer greater
  than `a (n - 1)` that is uniquely `a i + a j` with `i < j < n`.
* Checked in Python on the Ulam numbers up to `200000`: the gaps `d ≤ 33` that do not occur are
  exactly the eleven numbers above (the "if" direction for the other `d ≤ 33` is thus witnessed
  by early terms; the "only if" direction is the open part).
-/

namespace OMA.S_oeis_a072540

/-- `m` has a unique representation as `a i + a j` with `i < j < n`. -/
def UniqueUlamSum (a : ℕ → ℕ) (n m : ℕ) : Prop :=
  ∃! p : ℕ × ℕ, p.1 < p.2 ∧ p.2 < n ∧ m = a p.1 + a p.2

/-- `a` is the Ulam sequence A002858 (indexed from `0`). -/
def IsUlamSequence (a : ℕ → ℕ) : Prop :=
  a 0 = 1 ∧ a 1 = 2 ∧
  ∀ n, 2 ≤ n →
    a (n - 1) < a n ∧
    UniqueUlamSum a n (a n) ∧
    ∀ m, a (n - 1) < m → m < a n → ¬ UniqueUlamSum a n m

/-- The conjectured initial segment of A072540: the positive integers `d ≤ 33` that are not
differences between successive Ulam numbers are exactly `6, 11, 14, 16, 18, 21, 23, 26, 28, 31, 33`. -/
theorem main : ∀ a : ℕ → ℕ, IsUlamSequence a → ∀ d : ℕ, 1 ≤ d → d ≤ 33 →
    ((¬ ∃ n, a (n + 1) - a n = d) ↔
      d ∈ ({6, 11, 14, 16, 18, 21, 23, 26, 28, 31, 33} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a072540
