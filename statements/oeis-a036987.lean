import Mathlib

/-!
# A036987: Fredholm-Rueppel sequence.

Source: https://oeis.org/A036987
Credit: @Solfanbtc

Conjecture (Mats Granvik, OEIS A036987, formula section, Mar 04 2013):
a(n) = Sum_{k=1..n} A191898(n,k)*cos(Pi*(n-1)*(k-1))/n.
Status: the entry records that the conjecture is true (Sela Fried, Nov 25 2025, see the Fried
link in the entry); it is stated here as the source gives it.

Conventions:
* A036987 (offset 0) is the Fredholm-Rueppel sequence: a(m) = 1 if m + 1 is a power of 2,
  else 0 (1, 1, 0, 1, 0, 0, 0, 1, ...; characteristic function of A000225 = 2^k - 1).
* A191898 is the symmetric array T(n, 1) = T(1, k) = 1, T(n, k) = -Sum_{i=1..k-1} T(n-i, k)
  for n ≥ k, T(n, k) = -Sum_{i=1..n-1} T(k-i, n) for n < k (indices from 1; the value at an
  index 0 is never used).
* Minimal fix (index shift): the sum in the formula runs over k = 1..n and divides by n, so
  n ≥ 1; with the entry's offset 0 the identity fails at n = 2 (the right side is
  (T(2,1) - T(2,2))/2 = 1 but a(2) = 0). It holds with the 1-based indexing of the terms,
  i.e. the right side equals A036987(n - 1); checked in Python for 1 ≤ n < 80. So the
  statement is: for every n ≥ 1, A036987(n - 1) = Sum_{k=1..n} T(n,k) cos(π(n-1)(k-1)) / n.
-/

namespace OMA.S_oeis_a036987

/-- The Fredholm-Rueppel sequence A036987 (offset 0): `1` iff `m + 1` is a power of `2`. -/
noncomputable def A036987 (m : ℕ) : ℕ := by
  classical
  exact if ∃ j : ℕ, m + 1 = 2 ^ j then 1 else 0

/-- The array A191898 (indices from 1; `0` at an index `0`). -/
def T (n k : ℕ) : ℤ :=
  if h0 : n = 0 ∨ k = 0 then 0
  else if h1 : k = 1 ∨ n = 1 then 1
  else if hk : k ≤ n then -∑ i : Fin k, (if h : (i : ℕ) = 0 then 0 else T (n - i) k)
  else -∑ i : Fin n, (if h : (i : ℕ) = 0 then 0 else T (k - i) n)
termination_by n + k
decreasing_by all_goals (have := i.isLt; omega)

/-- Granvik's formula (proved by Fried), with the terms indexed from 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    (A036987 (n - 1) : ℝ) =
      ∑ k ∈ Finset.Icc 1 n,
        (T n k : ℝ) * Real.cos (Real.pi * ((n : ℝ) - 1) * ((k : ℝ) - 1)) / n := by
  sorry

end OMA.S_oeis_a036987
