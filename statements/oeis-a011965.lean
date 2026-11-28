import Mathlib

/-!
# A011965: Second differences of Bell numbers.

Source: https://oeis.org/A011965
Credit: @Solfanbtc

Conjecture (Mikhail Kurkov, Jan 27 2022, in the entry): a(n) = Sum_{k=0..2^n - 1} b(k) for
n >= 0, where b(0) = b(1) = 1 and, for n > 0,
  b(2n+1) = b(n) + b(A025480(n-1)),
  b(2n)   = b(n - 2^f(n)) + b(2n - 2^f(n)) + b(A025480(n-1)),
with f(n) = A007814(n) (the 2-adic valuation of n). Also b((4^n - 1)/3) = A141154(n+1).
`main` is the conjunction of both claims.

Conventions.
* a(n) = B(n+2) - 2 B(n+1) + B(n) (offset 0; second differences of the Bell numbers
  `Nat.bell`, as in the formula a(n) = A000110(n) - 2*A000110(n-1) + A000110(n-2) with the
  index shifted to offset 0: 1, 2, 7, 27, 114, ...).
* A025480(k): a(2k) = k, a(2k+1) = a(k); equivalently (entry formula) ((k+1)/2^v - 1)/2 with
  v = 2-adic valuation of k+1, which is what is used below.
* A141154 is defined by its L.g.f.: log(1 + Sum_{n>=1} (n-1)! x^n) = Sum_{n>=1} A141154(n) x^n/n.
  Differentiating, with F = 1 + Sum_{n>=1} (n-1)! x^n, this says
  Sum_{m>=0} A141154(m+1) x^m = F'/F, i.e. (Sum_m A141154(m+1) x^m) * F = F'
  (F is invertible). So "b((4^m-1)/3) = A141154(m+1) for all m" is stated as
  (Sum_m b((4^m-1)/3) x^m) * F = F' in ℚ⟦x⟧.
* Checked with python3: Sum_{k<2^n} b(k) equals the data for n = 0..16, and
  b((4^n-1)/3) = 1, 1, 4, 17, 91, 574, 4173, 34353, 316012 = A141154(1..9).
-/

namespace OMA.S_oeis_a011965

/-- A011965 (offset 0): second differences of the Bell numbers. -/
def a (n : ℕ) : ℤ := (Nat.bell (n + 2) : ℤ) - 2 * Nat.bell (n + 1) + Nat.bell n

/-- A025480: a(2k) = k, a(2k+1) = a(k). -/
def A025480 (k : ℕ) : ℕ := ((k + 1) / 2 ^ (k + 1).factorization 2 - 1) / 2

/-- Kurkov's auxiliary sequence `b`. -/
def b (m : ℕ) : ℕ :=
  if h : m ≤ 1 then 1
  else if m % 2 = 1 then b (m / 2) + b (A025480 (m / 2 - 1))
  else b (m / 2 - 2 ^ (m / 2).factorization 2) + b (m - 2 ^ (m / 2).factorization 2)
    + b (A025480 (m / 2 - 1))
decreasing_by
  all_goals first
    | omega
    | (have := Nat.one_le_two_pow (n := (m / 2).factorization 2); omega)
    | (have := Nat.div_le_self (m / 2 - 1 + 1) (2 ^ (m / 2 - 1 + 1).factorization 2)
       unfold A025480; omega)

open PowerSeries in
theorem main :
    (∀ n : ℕ, a n = ∑ k ∈ Finset.range (2 ^ n), (b k : ℤ)) ∧
    (let F : PowerSeries ℚ := PowerSeries.mk fun n => if n = 0 then 1 else ((n - 1).factorial : ℚ)
     PowerSeries.mk (fun m => (b ((4 ^ m - 1) / 3) : ℚ)) * F = PowerSeries.derivative ℚ F) := by
  sorry

end OMA.S_oeis_a011965
