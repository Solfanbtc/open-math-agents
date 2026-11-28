import Mathlib

/-!
# A068073: Period 4 sequence [ 1, 2, 3, 2, ...].

Source: https://oeis.org/A068073
Credit: @Solfanbtc

Conjecture (Paul Barry, Jan 14 2005, OEIS A068073):
  a(n) = Sum_{k=0..n} e^(i Pi (A000120(A001045(n)) - A001045(A000120(n)))).

Minimal fix: as printed, the summand does not depend on k, so the right side is (n+1) times a sign,
which fails at n = 3 (a(3) = 2, but 4 * (+-1) is not 2). The evident intent is that the summand
is evaluated at k: Sum_{k=0..n} e^(i Pi (A000120(A001045(k)) - A001045(A000120(k)))), which equals
1, 2, 3, 2, 1, 2, 3, 2, ... (checked for n < 300). `main` states this corrected form.

Definitions: a(n) is 1, 2, 3, 2 according to n mod 4 (offset 0); A000120(m) is the binary weight
of m; A001045(m) = (2^m - (-1)^m)/3 is the Jacobsthal sequence (an exact division in ℤ, always
>= 0, so `toNat` is harmless).
-/

namespace OMA.S_oeis_a068073

/-- The period-4 sequence 1, 2, 3, 2, ... -/
def a (n : ℕ) : ℕ := [1, 2, 3, 2].getD (n % 4) 0

/-- Binary weight (A000120). -/
def binWeight (m : ℕ) : ℕ := (Nat.digits 2 m).count 1

/-- Jacobsthal numbers (A001045). -/
def jacobsthal (m : ℕ) : ℤ := (2 ^ m - (-1) ^ m) / 3

theorem main : ∀ n : ℕ, (a n : ℂ) = ∑ k ∈ Finset.range (n + 1),
    Complex.exp (Complex.I * Real.pi *
      (((binWeight (jacobsthal k).toNat : ℤ) - jacobsthal (binWeight k) : ℤ) : ℂ)) := by
  sorry

end OMA.S_oeis_a068073
