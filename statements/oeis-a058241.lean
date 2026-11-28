import Mathlib

/-!
# A058241: Circular arrangements whose adjacent sums form {1, 2, …, n^2 - n + 1}

Source: https://oeis.org/A058241
Credit: @Solfanbtc

`a(n)` (offset 1) is the number of sets of `n` positive integers that can be placed along a circle
such that the set of sums of adjacent integers (sums over arcs of consecutive positions) is
`{1, 2, …, n^2 - n + 1}`: `1, 1, 1, 2, 1, 5, 0, 6, 4, 6, 0, 18, …`. Example: `{1, 2, 4}` placed as
`(1, 4, 2)` gives the sums `1, 2, 3, 4, 5, 6, 7`. Arcs: for each starting position and each length
`1, …, n` (length `n` is the whole circle; there are `n(n-1) + 1` distinct arcs).

Formalization: an arrangement is a list `x` without repetitions (positions around the circle),
its arc sums are `∑_{j<ℓ} x[(i+j) mod n]` for `i < n`, `1 ≤ ℓ ≤ n`; a set `S` is counted when some
arrangement of `S` has arc-sum set equal to `{1, …, n^2-n+1}`.

Conjecture (Zhao Hui Du, Mar 18 2019, OEIS comment): for `n > 2`, `p` prime, `e > 0`, if `n - 1` is
of the form `p^e` then `a(n) = A000010(n^2 - n + 1)/(6e)`, otherwise `a(n) = 0` (stated with the
division multiplied out, which includes its exactness). This refines the older comment
"if `n - 1` is of the form `p^e` then `a(n) > 0`, otherwise `a(n) = 0`", which is the prime power
conjecture for cyclic projective planes (such a set is a perfect difference set modulo
`n^2 - n + 1`): its first half is Singer's theorem and its second half follows from the prime power
conjecture for projective planes (upstream `Erdos723.erdos_723`); Du's exact count is not implied
by them. The formula agrees with every data term (`φ(7)/6 = 1`, `φ(13)/6 = 2`, `φ(21)/12 = 1`,
`φ(31)/6 = 5`, `φ(57)/6 = 6`, `φ(73)/18 = 4`, …, `φ(381)/6 = 42`, and `0` at `n = 7, 11, 13, 15,
16, 19, 21, 22, 23`).
-/

namespace OMA.S_oeis_a058241

/-- The set of arc sums of the circular arrangement `x`. -/
def arcSums (x : List ℕ) : Finset ℕ :=
  ((Finset.range x.length) ×ˢ (Finset.Icc 1 x.length)).image fun p =>
    ∑ j ∈ Finset.range p.2, x.getD ((p.1 + j) % x.length) 0

/-- `S` can be placed along a circle with arc sums exactly `{1, …, |S|^2 - |S| + 1}`. -/
def IsCircular (S : Finset ℕ) : Prop :=
  ∃ x : List ℕ, x.Nodup ∧ x.toFinset = S ∧
    arcSums x = Finset.Icc 1 (S.card ^ 2 - S.card + 1)

/-- A058241. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {S : Finset ℕ | S.card = n ∧ (∀ s ∈ S, 0 < s) ∧ IsCircular S}

/-- Du's conjecture: for `n > 2`, `a(n) = φ(n^2-n+1)/(6e)` if `n - 1 = p^e`, else `a(n) = 0`. -/
theorem main : ∀ n : ℕ, 2 < n →
    (∀ p e : ℕ, p.Prime → 0 < e → n - 1 = p ^ e →
      6 * e * a n = Nat.totient (n ^ 2 - n + 1)) ∧
    ((¬ ∃ p e : ℕ, p.Prime ∧ 0 < e ∧ n - 1 = p ^ e) → a n = 0) := by
  sorry

end OMA.S_oeis_a058241
