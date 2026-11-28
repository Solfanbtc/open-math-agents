import Mathlib

/-!
# A030127: the k-Somos sequence first becomes nonintegral at term 2k or 2k + 1

Source: https://oeis.org/A030127
Credit: @Solfanbtc

The `k`-Somos sequence: `s(0) = … = s(k-1) = 1` and, for `m ≥ k`,
`s(m) = (Sum_{j=1..floor(k/2)} s(m-j) s(m-k+j)) / s(m-k)`.
A030127 (offset 8): `a(k)` is the index of the first nonintegral term of the `k`-Somos
sequence. Data 17, 19, 20, 22, 24, 27, 28, … (`a(8) = 17`: Somos-8 first fails at `s(17)`.)

Conjecture (P. D. Hanna, Dec 08 2004): "for even terms, a(n) = 2*n, else a(n) = 2*n+1 when n is in
A101591", where A101591 lists the positions of the odd terms. Since A101591 is defined as those
positions, the content of the conjecture is that `a(k) ∈ {2k, 2k + 1}` for every `k ≥ 8`. This
includes that `a(k)` is defined (M. Somos, 2014: "There does not seem to be a published proof
that a(n) is defined for all n>=8"). `main` states: for every `k ≥ 8` there is a first
nonintegral term, and its index is `2k` or `2k + 1`.

Lean details. The terms are rationals, built by appending one term at a time to the list of the
`k` initial ones; `somos k m` is entry `m` of the list after `m` steps (that list has `k + m`
entries). All terms are positive, so the division never meets Lean's `x / 0 = 0`.
Checked with python3 (exact rationals): this reproduces the 30 listed terms, all in `{2k, 2k+1}`.
-/

namespace OMA.S_oeis_a030127

/-- Append the next term of the `k`-Somos recurrence to the list `l` of the terms so far. -/
def extend (k : ℕ) (l : List ℚ) : List ℚ :=
  let m := l.length
  l ++ [(∑ j ∈ Finset.Icc 1 (k / 2), l.getD (m - j) 0 * l.getD (m - k + j) 0) / l.getD (m - k) 0]

/-- The `m`-th term `s(m)` of the `k`-Somos sequence (for `k ≥ 1`). -/
def somos (k m : ℕ) : ℚ := ((extend k)^[m] (List.replicate k 1)).getD m 0

/-- `i` is the index of the first nonintegral term of the `k`-Somos sequence. -/
def FirstNonintegral (k i : ℕ) : Prop :=
  (somos k i).den ≠ 1 ∧ ∀ j < i, (somos k j).den = 1

/-- Hanna's conjecture: for `k ≥ 8`, the `k`-Somos sequence first becomes nonintegral at term
`2k` or `2k + 1`. -/
theorem main : ∀ k : ℕ, 8 ≤ k → ∃ i, FirstNonintegral k i ∧ (i = 2 * k ∨ i = 2 * k + 1) := by
  sorry

end OMA.S_oeis_a030127
