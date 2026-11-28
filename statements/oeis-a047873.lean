import Mathlib

/-!
# A047873: a(n) = max_{r=1..n-1} ceiling(t(t(n)-t(r-1))/(n-r+1)), where t() = triangular numbers A000217.

Source: https://oeis.org/A047873
Credit: @Solfanbtc

Conjecture (OEIS A047873, A047837): this lower bound for Honaker's triangle problem (A047837)
is the exact value, i.e. A047837(n) = A047873(n) for all n ≥ 1 (A047837 says they agree at least
for n < 365).

Honaker's triangle problem (A047837): form a triangle with base of length n (rows of lengths
n, n-1, ..., 1), all entries different, all row sums equal; A047837(n) is the minimal row sum.
Entries are positive integers, as in the examples of A047837 (e.g. n = 4: 15; 7 8; 4 5 6;
1 2 3 9, row sum 15). Here row `i` (for `i < n`) has length `n - i`, and an entry is indexed by
`⟨i, j⟩` with `j < n - i`.

Minimal fix of the range of `r`. Read literally, `max_{r=1..n-1}` is an empty maximum at n = 1,
while the OEIS data gives a(1) = 1. We take the maximum over `r = 1..n` instead. The extra term
`r = n` equals `t(n)`, which never exceeds the `r = n - 1` term `ceiling(t(2n-1)/2)` when
n ≥ 2 (since (2n-1)n/2 ≥ n(n+1)/2), so the values agree with the name's formula for every
n ≥ 2, and at n = 1 the value is t(1) = 1, matching the data. Checked numerically against all
40 listed terms. The ceiling of p/q for q ≥ 1 is computed as `(p + q - 1) / q`.
-/

namespace OMA.S_oeis_a047873

/-- Triangular numbers A000217. -/
def t (k : ℕ) : ℕ := k * (k + 1) / 2

/-- A047873, offset 1 (maximum over `r = 1..n`, see the module docstring). -/
def a (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).sup fun r => (t (t n - t (r - 1)) + (n - r + 1) - 1) / (n - r + 1)

/-- A Honaker triangle with base `n` and row sum `S`: distinct positive integer entries, row `i`
(for `i < n`) of length `n - i`, every row summing to `S`. -/
def IsHonakerTriangle (n S : ℕ) : Prop :=
  ∃ f : (Σ i : Fin n, Fin (n - i)) → ℕ,
    Function.Injective f ∧ (∀ x, 0 < f x) ∧ ∀ i : Fin n, ∑ j : Fin (n - i), f ⟨i, j⟩ = S

/-- A047837: the minimal row sum of a Honaker triangle with base `n`. -/
noncomputable def honaker (n : ℕ) : ℕ := sInf {S : ℕ | IsHonakerTriangle n S}

theorem main : ∀ n : ℕ, 1 ≤ n → honaker n = a n := by
  sorry

end OMA.S_oeis_a047873
