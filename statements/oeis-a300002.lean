import Mathlib

/-!
# A300002: Lexicographically earliest sequence of positive integers such that no k+2 points fall on any polynomial of degree k.

Source: https://oeis.org/A300002
Credit: @Solfanbtc

`a(1), a(2), ...` (offset 1) is the lexicographically earliest sequence of positive integers such
that no `k + 2` of the points `(n, a(n))` lie on a polynomial of degree `k`, for any `k ≥ 0`.
Data: `1, 2, 4, 3, 6, 5, 9, 16, 14, 20, 7, 15, 8, ...`.

Conjecture (the entry): this sequence is a permutation of the natural numbers (the positive
integers, the values it takes).

Conventions:
* "a polynomial of degree k" is read as degree `≤ k` (rational coefficients): if `k + 2` points lie
  on a polynomial of degree `j < k`, then already `j + 2` of them lie on a polynomial of degree
  `j`, so both readings give the same sequence. Real coefficients would also give the same
  condition, since an interpolating polynomial through rational points is rational.
* `Good f n`: among the points `(i, f i)`, `1 ≤ i ≤ n`, no set `S` of `|S| ≥ 2` of them lies on a
  polynomial of degree `≤ |S| - 2`.
* The sequence is characterized rather than constructed: `IsLexEarliest f` says that for every
  `n ≥ 1`, `f n ≥ 1`, the prefix up to `n` is good, and no smaller positive value at position `n`
  (with the same earlier terms) keeps it good. This determines `f` on `n ≥ 1` by induction, and
  such an `f` exists since at each step only finitely many values are excluded (one per nonempty
  subset of earlier points, as the entry notes).
* A python3 check (each nonempty subset of earlier points forbids the value of its interpolating
  polynomial at `n`) reproduces the first 18 data terms.
-/

namespace OMA.S_oeis_a300002

/-- No `|S| ≥ 2` of the points `(i, f i)`, `1 ≤ i ≤ n`, lie on a polynomial of degree
`≤ |S| - 2`. -/
def Good (f : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ S ⊆ Finset.Icc 1 n, 2 ≤ S.card →
    ¬ ∃ P : Polynomial ℚ, P.natDegree ≤ S.card - 2 ∧ ∀ i ∈ S, P.eval (i : ℚ) = (f i : ℚ)

/-- `f` restricted to positive indices is the lexicographically earliest good sequence of
positive integers. -/
def IsLexEarliest (f : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → 1 ≤ f n ∧ Good f n ∧
    ∀ v : ℕ, 1 ≤ v → v < f n → ¬ Good (Function.update f n v) n

/-- Conjecture: A300002 is a permutation of the positive integers. -/
theorem main : ∀ f : ℕ → ℕ, IsLexEarliest f → Set.BijOn f {n | 1 ≤ n} {v | 1 ≤ v} := by
  sorry

end OMA.S_oeis_a300002
