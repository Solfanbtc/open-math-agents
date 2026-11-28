import Mathlib

/-!
# A000698: A problem of configurations: a(0) = 1; for n>0, a(n) = (2n-1)!! - Sum_{k=1..n-1} (2k-1)!! a(n-k).

Source: https://oeis.org/A000698
Credit: @Solfanbtc

Claim (Peter Bala, Dec 22 2011, in the entry), which settles a conjecture of G. A. Edgar
(Transseries for beginners, Problem 4.32): the o.g.f. B(x) = Sum_{n>=1} a(n) x^(2n-1)
= x + 2x^3 + 10x^5 + 74x^7 + ... satisfies the Riccati differential equation
y'(x) = -1/x^2 + (1/x^3) y(x) - (1/x^2) y(x)^2 with y(0) = 0; hence b(x) = -B(1/x) satisfies
b'(x) = -1 - (x + b(x)) b(x), and the differential operator D^2 + x D + 1 (D = d/dx)
factorizes as (D - a(x)) (D - b(x)) with a(x) = -(x + b(x)). The entry reports Edgar's
conjecture as proved by this (Bala's derivation).

Conventions.
* `a` is defined exactly by the recursion of the name (computed in ℤ, since the recursion has a
  subtraction); it reproduces the listed terms 1, 1, 2, 10, 74, 706, ... (checked with python3).
* B is the formal power series with coefficient a(n) at x^(2n-1) (n ≥ 1) and 0 at even powers,
  so B(0) = 0, the initial condition.
* Why this single identity is the whole claim. Multiplying the Riccati equation by x^3 gives the
  identity of formal power series `x^3 B' = -x + B - x B^2` (ℤ⟦x⟧ is a domain, so no
  information is lost). With t = 1/x and b(x) = -B(t), one has d/dx = -t^2 d/dt and the
  equation b' = -1 - (x + b) b becomes t^2 B'(t) = -1 + B(t)/t - B(t)^2, i.e. the same identity
  divided by t. Finally (D - a)(D - b) f = f'' - (a + b) f' + (a b - b') f, and with
  a = -(x + b) this is f'' + x f' + (-(x + b) b - b') f, which equals (D^2 + x D + 1) f for all
  f exactly when b' = -1 - (x + b) b. So the factorization (Edgar's conjecture, in Bala's form)
  is equivalent to the identity stated below.
* Checked with python3: the identity holds coefficientwise through degree 57.
-/

namespace OMA.S_oeis_a000698

open PowerSeries

/-- The list `[a 0, ..., a n]`, by the defining recursion
`a(0) = 1`, `a(n) = (2n-1)!! - ∑_{k=1}^{n-1} (2k-1)!! a(n-k)`. -/
def aList : ℕ → List ℤ
  | 0 => [1]
  | n + 1 =>
    let L := aList n
    L ++ [((Nat.doubleFactorial (2 * n + 1) : ℕ) : ℤ) -
      ∑ k ∈ Finset.Icc 1 n, ((Nat.doubleFactorial (2 * k - 1) : ℕ) : ℤ) * L.getD (n + 1 - k) 0]

/-- A000698. -/
def a (n : ℕ) : ℤ := (aList n).getD n 0

/-- B(x) = ∑_{n ≥ 1} a(n) x^(2n-1). -/
def B : ℤ⟦X⟧ := PowerSeries.mk fun m => if m % 2 = 1 then a ((m + 1) / 2) else 0

theorem main : X ^ 3 * derivative ℤ B = -X + B - X * B ^ 2 := by
  sorry

end OMA.S_oeis_a000698
