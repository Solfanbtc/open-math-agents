import Mathlib

/-!
# A071684: Number of plane trees with n edges and having an odd number of leaves.

Source: https://oeis.org/A071684
Credit: @Solfanbtc

Conjecture (R. J. Mathar, Jul 05 2018, OEIS A071684): for n >= 5 (offset 1, so that a(n-4) is a
term),
  n(n+1)(10n-37) a(n) + 2n(5n^2-42n+91) a(n-1) + 4(-40n^3+270n^2-560n+357) a(n-2)
  + 8(n-3)(5n^2-42n+91) a(n-3) - 16(n-4)(25n-51)(2n-7) a(n-4) = 0.

Definition. The number of plane trees with n >= 1 edges and k leaves is the Narayana number
N(n, k) = binomial(n, k) binomial(n, k-1) / n (classical; this is the formula of Paul Barry in the
entry, a(n) = Σ_{k=1..n} (1/n) C(n,k) C(n,k-1) (1 - (-1)^k)/2, and the "Narayana transform"
comment). So a(n) = Σ_{k odd, 1 <= k <= n} N(n, k). The division by n is exact.
Checked numerically: reproduces the listed terms 1, 1, 2, 7, 22, 66, ..., and the recurrence holds
for 5 <= n < 200.
-/

namespace OMA.S_oeis_a071684

/-- Narayana number: plane trees with `n` edges and `k` leaves (n ≥ 1). -/
def narayana (n k : ℕ) : ℕ := n.choose k * n.choose (k - 1) / n

/-- a(n): plane trees with `n` edges and an odd number of leaves. -/
def a (n : ℕ) : ℕ := ∑ k ∈ (Finset.Icc 1 n).filter Odd, narayana n k

theorem main : ∀ n : ℕ, 5 ≤ n →
    (n : ℤ) * (n + 1) * (10 * n - 37) * a n + 2 * (n : ℤ) * (5 * n ^ 2 - 42 * n + 91) * a (n - 1)
      + 4 * (-40 * (n : ℤ) ^ 3 + 270 * n ^ 2 - 560 * n + 357) * a (n - 2)
      + 8 * ((n : ℤ) - 3) * (5 * n ^ 2 - 42 * n + 91) * a (n - 3)
      - 16 * ((n : ℤ) - 4) * (25 * n - 51) * (2 * n - 7) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a071684
