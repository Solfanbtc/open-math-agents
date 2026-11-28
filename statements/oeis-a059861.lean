import Mathlib

/-!
# A059861: a(n) = Product_{i=2..n} (prime(i) - 2).

Source: https://oeis.org/A059861
Credit: @Solfanbtc

Claim in the entry: a(n) is the exact number of d = 2 and also of d = 4 differences in
dRRS[modulus = n-th primorial] (A049296: first differences of the reduced residue system
modulo m, over one period). This is a known (elementary, CRT) fact rather than an open problem;
Greg Tener's formula in the entry, a(n) = |{r : 0 ≤ r < primorial(n), gcd(r, primorial(n)) = 1,
gcd(r+2, primorial(n)) = 1}|, is the d = 2 half.

Conventions.
* prime(i) is 1-indexed in the entry; `Nat.nth Nat.Prime i` is 0-indexed, so
  a(n) = ∏_{i=1}^{n-1} (nth prime i - 2) and the n-th primorial is m = ∏_{i<n} nth prime i.
* One period of dRRS[m] consists of the gaps between consecutive reduced residues taken
  cyclically (the entry's example: for m = 210 the 48 gaps contain fifteen 2's and fifteen
  4's; for m = 6 the period is {4, 2}). A gap 2 starts at each reduced residue r with r + 2
  also reduced (r + 1 is even, hence never reduced, as m is even); a gap 4 starts at each r
  with r, r + 4 reduced and r + 2 not reduced (r + 1, r + 3 are even). Residues are taken
  modulo m via gcd with m.
* Range. For n = 1 (m = 2) the period is {2}: one gap 2 but no gap 4, while a(1) = 1, so the
  "also d = 4" part fails at this trivial value; the minimal fix states it for n ≥ 2.
  (python3: both counts equal a(n) for n = 2..6; the d = 2 count is a(n) also for n = 1.)
-/

namespace OMA.S_oeis_a059861

/-- The n-th primorial: the product of the first n primes. -/
noncomputable def primorialN (n : ℕ) : ℕ := ∏ i ∈ Finset.range n, Nat.nth Nat.Prime i

/-- A059861. -/
noncomputable def a (n : ℕ) : ℕ := ∏ i ∈ Finset.Ico 1 n, (Nat.nth Nat.Prime i - 2)

theorem main : ∀ n : ℕ, 2 ≤ n →
    ((Finset.range (primorialN n)).filter (fun r =>
        Nat.Coprime r (primorialN n) ∧ Nat.Coprime (r + 2) (primorialN n))).card = a n ∧
    ((Finset.range (primorialN n)).filter (fun r =>
        Nat.Coprime r (primorialN n) ∧ ¬ Nat.Coprime (r + 2) (primorialN n) ∧
          Nat.Coprime (r + 4) (primorialN n))).card = a n := by
  sorry

end OMA.S_oeis_a059861
