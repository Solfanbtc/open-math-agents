import Mathlib

/-!
# A032908: positive solutions of ab ∣ (a+b)(a+b+1) are consecutive terms of A032908 or A101265

Source: https://oeis.org/A032908
Credit: @Solfanbtc

A032908 (offset 0): 2, 2, 3, 6, 14, 35, 90, …, with `a(n) = 4a(n-1) - 4a(n-2) + a(n-3)` (from its
g.f. `(2 - 6x + 3x^2)/((1 - x)(1 - 3x + x^2))`); also `a(n) = F(2n-1) + 1`.
A101265 (offset 1): `a(1) = 1, a(2) = 2, a(3) = 6`, `a(n) = 5a(n-1) - 5a(n-2) + a(n-3)`;
1, 2, 6, 21, 77, ….

Conjecture (R. Israel, Aug 26 2015): "consecutive terms of this sequence and consecutive terms
of A101265 provide all the positive integer solutions of (a+b)*(a+b+1) == 0 (mod (a*b))."
Status: "Conjecture is true: see Mathematics Stack Exchange link" (R. Israel, Sep 06 2015).

Minimal fix. Read literally (with the listed offsets) the claim misses one solution: `(1, 1)`
(`1 ∣ 6`), which is not a pair of consecutive terms of either sequence. It corresponds to the
extra initial term `a(0) = 1` of A101265 used in its formula `a(n+1) = a(n)(a(n) + 1)/a(n-1)`
(P. D. Hanna). `main` states: for positive `a, b`, `ab ∣ (a+b)(a+b+1)` iff `(a, b) = (1, 1)` or
`{a, b}` is a pair of consecutive terms of A032908 or of A101265 (in either order, since the
condition is symmetric). Checked with python3: for `1 ≤ a, b < 3000` the solutions are exactly
these pairs together with `(1, 1)`, and every consecutive pair is a solution.
-/

namespace OMA.S_oeis_a032908

/-- A032908: `s 0 = 2, s 1 = 2, s 2 = 3`, `s (n+3) = 4 s(n+2) - 4 s(n+1) + s n`. -/
def s : ℕ → ℤ
  | 0 => 2
  | 1 => 2
  | 2 => 3
  | n + 3 => 4 * s (n + 2) - 4 * s (n + 1) + s n

/-- A101265, shifted: `t m = A101265(m+1)`; `t 0 = 1, t 1 = 2, t 2 = 6`,
`t (m+3) = 5 t(m+2) - 5 t(m+1) + t m`. -/
def t : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | 2 => 6
  | n + 3 => 5 * t (n + 2) - 5 * t (n + 1) + t n

/-- `{a, b}` is a pair of consecutive terms of the sequence `u`, in either order. -/
def ConsecPair (u : ℕ → ℤ) (a b : ℤ) : Prop :=
  ∃ n, (a = u n ∧ b = u (n + 1)) ∨ (a = u (n + 1) ∧ b = u n)

/-- Israel's theorem (with the solution `(1, 1)` added). -/
theorem main : ∀ a b : ℤ, 0 < a → 0 < b →
    (a * b ∣ (a + b) * (a + b + 1) ↔
      (a = 1 ∧ b = 1) ∨ ConsecPair s a b ∨ ConsecPair t a b) := by
  sorry

end OMA.S_oeis_a032908
