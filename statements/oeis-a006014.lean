import Mathlib

/-!
# A006014: a(n+1) = (n+1)*a(n) + Sum_{k=1..n-1} a(k)*a(n-k).

Source: https://oeis.org/A006014
Credit: @Solfanbtc

Conjecture (OEIS A006014, formula section, Mikhail Kurkov, Nov 19 2021, rewritten
Mar 27 2026): a(n) = Sum_{k=0..2^(n-1) - 1} A379818(k).

Definitions:
* A006014 has offset 1 with a(1) = 1 (all programs of the entry) and
  a(n+1) = (n+1)*a(n) + Sum_{k=1..n-1} a(k)*a(n-k) for n >= 1. Here `a 0 = 0` is a filler
  value never used by the recursion or the statement.
* A379818: b(0) = 1, b(2n+1) = b(n) for n >= 0, and for n > 0
  b(2n) = b(n) + b(n - 2^f(n)) + b(2n - 2^f(n)) + b(A025480(n-1)), f(n) = A007814(n) the
  2-adic valuation of n. Here A025480(n-1) (A025480: c(2m) = m, c(2m+1) = c(m)) equals
  (oddpart(n) - 1)/2 = floor(n / 2^(f(n)+1)), the form used in the PARI program of A379818.
* Evaluated with `#eval`, `a` gives 1, 2, 7, 32, 178, 1160, 8653, 72704 and `b` gives
  1, 1, 4, 1, 10, 4, 10, 1, 22, 10, 28, 4, 49, ..., matching both data sections. The
  conjecture holds for 1 <= n <= 21 (Python check).
-/

namespace OMA.S_oeis_a006014

/-- A006014 (offset 1; `a 0 = 0` is unused). -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => (n + 2) * a (n + 1) +
      ∑ k : Fin (n + 1), if h : 1 ≤ (k : ℕ) then
        (have : (k : ℕ) < n + 2 := by omega
         have : n + 1 - k < n + 2 := by omega
         a k * a (n + 1 - k)) else 0

/-- A379818. -/
def b (m : ℕ) : ℕ :=
  if h0 : m = 0 then 1
  else if h1 : m % 2 = 1 then
    (have : m / 2 < m := by omega
     b (m / 2))
  else
    have hA : 1 ≤ 2 ^ ((m / 2).factorization 2) := Nat.one_le_two_pow
    have hle : 2 ^ ((m / 2).factorization 2) ≤ m / 2 :=
      Nat.le_of_dvd (by omega) (Nat.ordProj_dvd (m / 2) 2)
    have : m / 2 < m := by omega
    have : m / 2 - 2 ^ ((m / 2).factorization 2) < m := by omega
    have : m - 2 ^ ((m / 2).factorization 2) < m := by omega
    have : m / 2 / (2 * 2 ^ ((m / 2).factorization 2)) < m :=
      lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
    b (m / 2) + b (m / 2 - 2 ^ ((m / 2).factorization 2)) +
      b (m - 2 ^ ((m / 2).factorization 2)) +
      b (m / 2 / (2 * 2 ^ ((m / 2).factorization 2)))
termination_by m

/-- Kurkov's conjecture: `a(n) = ∑_{k < 2^(n-1)} A379818(k)` for `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = ∑ k ∈ Finset.range (2 ^ (n - 1)), b k := by
  sorry

end OMA.S_oeis_a006014
