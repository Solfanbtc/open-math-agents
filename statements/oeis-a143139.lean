import Mathlib

/-!
# A143139: E.g.f.: A(x) = exp(x + A(x)^2) - 1.

Source: https://oeis.org/A143139
Credit: @Solfanbtc

Claim (entry comment, conjectured by Peter Bala, Feb 2026): for every positive integer k, the
sequence a(n) reduced modulo k is eventually periodic with period dividing φ(k). Stated as: there
is N with a(n + φ(k)) ≡ a(n) (mod k) for all n ≥ N; an eventual period dividing φ(k) is the same
as φ(k) being an eventual period. (Example from the entry: modulo 14 the period 6 = φ(14) starts
at n = 2.)

Definition. A(x) = Σ_{n≥1} a(n) x^n/n! is the power series with A(0) = 0 and
A = exp(x + A^2) - 1. Differentiating gives A' = (1 + A)(1 + 2A·A'), i.e.
A' = 1 + A + 2A·A' + 2A^2·A', and since that equation and A(0) = 0 determine A, it is equivalent.
Comparing coefficients of x^n/n! gives, with a(0) = 0,
a(n+1) = [n = 0] + a(n) + 2 Σ_{i=0..n} C(n,i) a(i) a(n+1-i)
         + 2 Σ_{i+j+l=n} n!/(i! j! l!) a(i) a(j) a(l+1),
where the right side only uses a(0..n) because a(0) = 0. A python run of this recurrence
reproduces all 18 listed terms 1, 3, 25, 351, 6901, ..., and the claim holds for every
k < 80 within n < 400.
-/

namespace OMA.S_oeis_a143139

/-- The next coefficient a(n+1) from the list `l = [a(0), ..., a(n)]`, by the recurrence above
(an index `n + 1` beyond the list reads as 0; it only occurs multiplied by a(0) = 0). -/
def next (n : ℕ) (l : List ℕ) : ℕ :=
  let b := fun m => l.getD m 0
  (if n = 0 then 1 else 0) + b n
    + 2 * ∑ i ∈ Finset.range (n + 1), n.choose i * b i * b (n + 1 - i)
    + 2 * ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1 - i),
        (n.factorial / (i.factorial * j.factorial * (n - i - j).factorial))
          * b i * b j * b (n - i - j + 1)

/-- `vals n = [a(0), ..., a(n)]`. -/
def vals : ℕ → List ℕ
  | 0 => [0]
  | n + 1 => vals n ++ [next n (vals n)]

/-- A143139(n): coefficient of x^n/n! in A(x) (`a 0 = 0`). -/
def a (n : ℕ) : ℕ := (vals n).getD n 0

theorem main : ∀ k : ℕ, 0 < k →
    ∃ N : ℕ, ∀ n ≥ N, a (n + Nat.totient k) % k = a n % k := by
  sorry

end OMA.S_oeis_a143139
