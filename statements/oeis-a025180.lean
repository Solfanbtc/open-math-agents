import Mathlib

/-!
# A025180: a(n) = number of (s(0), s(1), ..., s(n)) such that s(i) is an integer, s(0) = 0, |s(1)| = 1, |s(i) - s(i-1)| <= 1 for i >= 2, s(n) = 2.

Source: https://oeis.org/A025180
Credit: @Solfanbtc

Conjecture (R. J. Mathar, Feb 25 2015, OEIS A025180):
  -(n+2)(n-3) a(n) + 2(2n+1)(n-3) a(n-1) + (-n^2+10n-18) a(n-2) - 3(2n-3)(n-3) a(n-3) = 0,
stated for n >= 5, so that all indices lie in the range n >= 2 of the sequence (offset 2).

Definition. A sequence (s(0), ..., s(n)) as in the name is determined by s(1) = e ∈ {-1, 1} and
the steps d(i) = s(i) - s(i-1) ∈ {-1, 0, 1} for 2 <= i <= n, and s(n) = e + Σ d(i); this is a
bijection, so a(n) counts the pairs (e, d) with e + Σ d(i) = 2. Here e is encoded by `Bool`
(true ↦ 1, false ↦ -1) and the n - 1 steps by `Fin (n - 1) → Fin 3` (j ↦ j - 1).
Checked numerically: reproduces all 27 listed terms 1, 2, 7, 20, ..., and the recurrence holds
for 5 <= n < 80.
-/

namespace OMA.S_oeis_a025180

/-- The integer step encoded by `j : Fin 3`: `-1`, `0` or `1`. -/
def stepVal (j : Fin 3) : ℤ := (j : ℤ) - 1

/-- a(n) for n ≥ 1: number of walks s(0) = 0, |s(1)| = 1, then n - 1 steps in {-1, 0, 1},
ending at s(n) = 2. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun p : Bool × (Fin (n - 1) → Fin 3) =>
    (if p.1 then (1 : ℤ) else -1) + ∑ i, stepVal (p.2 i) = 2).card

theorem main : ∀ n : ℕ, 5 ≤ n →
    -((n : ℤ) + 2) * ((n : ℤ) - 3) * a n + 2 * (2 * (n : ℤ) + 1) * ((n : ℤ) - 3) * a (n - 1)
      + (-(n : ℤ) ^ 2 + 10 * n - 18) * a (n - 2)
      - 3 * (2 * (n : ℤ) - 3) * ((n : ℤ) - 3) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a025180
