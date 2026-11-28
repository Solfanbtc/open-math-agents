import Mathlib

/-!
# A133158: Binomial transform of A126568, second binomial transform of A026641.

Source: https://oeis.org/A133158
Credit: @Solfanbtc

Claim (entry formula, conjectured by R. J. Mathar, 2013): for n ≥ 3 (so that a(n-3) is defined,
offset 0),
2n·a(n) + (-19n+12)·a(n-1) + 6(8n-11)·a(n-2) + 36(-n+2)·a(n-3) = 0.

Definitions. A026641(j) = Σ_{k=0..j} (-1)^k C(2j-k, j) (a formula listed in A026641, which
reproduces its data 1, 1, 4, 13, 46, ...). A126568 is the binomial transform of A026641 and
A133158 the binomial transform of A126568, following the name literally:
a(n) = Σ_{j=0..n} C(n,j)·A126568(j). A python check with these definitions gives all 23 listed
terms 1, 3, 12, 57, ..., 12878508015774468, and the recurrence for 3 ≤ n < 400
(e.g. n = 3: 342 - 540 + 234 - 36 = 0).
-/

namespace OMA.S_oeis_a133158

/-- A026641(j) = Σ_{k=0..j} (-1)^k C(2j-k, j). -/
def A026641 (j : ℕ) : ℤ := ∑ k ∈ Finset.range (j + 1), (-1) ^ k * ((2 * j - k).choose j : ℤ)

/-- A126568: binomial transform of A026641. -/
def A126568 (n : ℕ) : ℤ := ∑ j ∈ Finset.range (n + 1), (n.choose j : ℤ) * A026641 j

/-- A133158: binomial transform of A126568. -/
def a (n : ℕ) : ℤ := ∑ j ∈ Finset.range (n + 1), (n.choose j : ℤ) * A126568 j

theorem main : ∀ n : ℕ, 3 ≤ n →
    2 * (n : ℤ) * a n + (-19 * (n : ℤ) + 12) * a (n - 1) + 6 * (8 * (n : ℤ) - 11) * a (n - 2)
      + 36 * (-(n : ℤ) + 2) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a133158
