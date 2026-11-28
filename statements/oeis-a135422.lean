import Mathlib

/-!
# A135422: a(1) = 1, a(n) = Sum(k=1,n-1, a(k)^F(n-k)) where F(m) is the m-th Fibonacci number.

Source: https://oeis.org/A135422
Credit: @Solfanbtc

Claim (entry comment, Gerald McGarvey): lim_{n→∞} Phi^(Phi^(n-c)) / a(n) = 1, where Phi is the
golden ratio and c = 3.47348961175710091... is a constant.

Stated as: there is a real c with 3.47348961175710091 ≤ c ≤ 3.47348961175710092 (the digits given,
truncated) such that Phi^(Phi^(n-c)) / a(n) → 1. If the limit holds, c is unique, since
changing c changes the ratio by a factor that tends to 0 or ∞.

Conventions: F(m) = `Nat.fib m` (F(1) = F(2) = 1), offset 1, a(1) = 1. A python check: the
recursion reproduces all 15 listed terms, and n - log_Phi(log_Phi a(n)) is 3.4734895880 at
n = 23, oscillating towards ≈ 3.4734896118 (consecutive errors shrink by about 1/Phi^2),
consistent with the stated value.
-/

namespace OMA.S_oeis_a135422

/-- `vals n = [a(1), ..., a(n+1)]`. -/
def vals : ℕ → List ℕ
  | 0 => [1]
  | n + 1 =>
    let l := vals n
    l ++ [∑ k ∈ Finset.range (n + 1), l.getD k 0 ^ Nat.fib (n + 1 - k)]

/-- A135422(n) for n ≥ 1 (`a 0` is an unused value). -/
def a (n : ℕ) : ℕ := (vals (n - 1)).getD (n - 1) 0

theorem main :
    ∃ c : ℝ, 3.47348961175710091 ≤ c ∧ c ≤ 3.47348961175710092 ∧
      Filter.Tendsto (fun n : ℕ => goldenRatio ^ (goldenRatio ^ ((n : ℝ) - c)) / (a n : ℝ))
        Filter.atTop (nhds 1) := by
  sorry

end OMA.S_oeis_a135422
