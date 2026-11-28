import Mathlib

/-!
# A026765: a(n) = Sum_{k=0..n} T(n,k), T given by A026758.

Source: https://oeis.org/A026765
Credit: @Solfanbtc

Three conjectures in the entry; `main` is their conjunction:
1. (Maksym Voznyy, Aug 11 2009) G.f.:
   -(1-2x-5x^2+10x^3 - sqrt(1-10x^2+29x^4-20x^6)) / (2x(1-2x-5x^2+10x^3)).
2. (R. J. Mathar, Jun 30 2013) (n+1) a(n) - 2 a(n-1) + 2(-5n+3) a(n-2) + 12 a(n-3)
   + (29n-71) a(n-4) - 10 a(n-5) + 20(-n+5) a(n-6) = 0.
3. (Vaclav Kotesovec, Feb 12 2014) a(n) ~ (2+sqrt(5) + (-1)^n (2-sqrt(5))) 5^(n/2) / sqrt(2 Pi n).

Conventions.
* T = A026758 by its defining recurrence: T(n,0) = T(n,n) = 1; for 1 ≤ k ≤ n-1,
  T(n,k) = T(n-1,k-1) + T(n-2,k-1) + T(n-1,k) if n is odd and k ≤ (n-1)/2, else
  T(n,k) = T(n-1,k-1) + T(n-1,k) (as in the entry's Maple/Mathematica programs).
  a(n) = Σ_{k=0}^{n} T(n,k), offset 0: 1, 2, 4, 9, 18, 41, ... (python3: matches the data).
* Conjecture 1. With A = Σ a(n) x^n, P = 1-2x-5x^2+10x^3, Q = 1-10x^2+29x^4-20x^6, the claim
  A = -(P - sqrt Q)/(2xP) means 2xP·A + P = sqrt Q, the power series square root with constant
  term 1. Since 2xP·A + P has constant term 1, this is equivalent to (2xP·A + P)^2 = Q in ℤ⟦x⟧,
  which is stated. (python3: holds up to x^59.)
* Conjecture 2 involves a(n-6), so it is stated for n ≥ 6 (python3: holds for 6 ≤ n < 400).
* Conjecture 3: the ratio tends to 1 (python3: 1.0186 at n = 100, 1.0029 at n = 399). The
  comparison function is positive for every n ≥ 1 (its first factor is 4 or 2√5).
-/

namespace OMA.S_oeis_a026765

/-- The triangle A026758 (0 for k > n). -/
def T : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | 1, k => if k ≤ 1 then 1 else 0
  | n + 2, k =>
    if n + 2 < k then 0
    else if k = 0 ∨ k = n + 2 then 1
    else if (n + 2) % 2 = 1 ∧ k ≤ (n + 1) / 2 then T (n + 1) (k - 1) + T n (k - 1) + T (n + 1) k
    else T (n + 1) (k - 1) + T (n + 1) k

/-- A026765: row sums of A026758. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), T n k

open PowerSeries in
theorem main :
    (let A : PowerSeries ℤ := PowerSeries.mk fun n => (a n : ℤ)
     let P : PowerSeries ℤ := 1 - 2 * X - 5 * X ^ 2 + 10 * X ^ 3
     (2 * X * P * A + P) ^ 2 = 1 - 10 * X ^ 2 + 29 * X ^ 4 - 20 * X ^ 6) ∧
    (∀ n : ℕ, 6 ≤ n →
      ((n : ℤ) + 1) * a n - 2 * a (n - 1) + 2 * (-5 * (n : ℤ) + 3) * a (n - 2) + 12 * a (n - 3)
        + (29 * (n : ℤ) - 71) * a (n - 4) - 10 * a (n - 5) + 20 * (-(n : ℤ) + 5) * a (n - 6)
        = 0) ∧
    Filter.Tendsto
      (fun n : ℕ => (a n : ℝ) /
        ((2 + Real.sqrt 5 + (-1) ^ n * (2 - Real.sqrt 5)) * Real.sqrt 5 ^ n
          / Real.sqrt (2 * Real.pi * n)))
      Filter.atTop (nhds 1) := by
  sorry

end OMA.S_oeis_a026765
