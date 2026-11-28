import Mathlib

/-!
# A039650: Prime reached by iterating f(x) = phi(x)+1 on n.

Source: https://oeis.org/A039650
Credit: @Solfanbtc

Conjecture (T. D. Noe, OEIS A039650, comment, Oct 17 2013, and A229487): A229487 gives the
conjectured largest number that converges to prime(n), i.e. A229487(n) is the greatest x whose
trajectory under x ↦ phi(x) + 1 reaches prime(n). In particular only finitely many numbers
converge to each listed prime.

Conventions:
* f(x) = phi(x) + 1 with Euler's totient (`Nat.totient`); for x > 1 the trajectory decreases
  until it reaches a prime, which is a fixed point (A039650, comment by N. J. A. Sloane);
  1 ↦ 2. "x converges to p" means f^[k](x) = p for some k ≥ 0, x ≥ 1.
* prime(n) is the n-th prime, `Nat.nth Nat.Prime (n - 1)` (offset 1).
* The claim is stated for every listed term of A229487 (all 53 terms of %S/%T/%U), as
  `IsGreatest`. Checked in Python: for every x ≤ 2·10^6 the limit of the trajectory was
  computed, and for each of the 53 primes the largest x ≤ 2·10^6 converging to it is the
  listed term.
-/

namespace OMA.S_oeis_a039650

/-- The listed terms of A229487. -/
def A229487 : List ℕ :=
  [2, 6, 12, 30, 22, 138, 60, 54, 46, 58, 62, 174, 498, 510, 94, 106, 118, 4314, 134, 142,
    1038, 158, 166, 276, 420, 250, 206, 214, 750, 1758, 254, 262, 274, 278, 298, 302,
    1182, 486, 334, 346, 358, 6360, 382, 1614, 394, 398, 422, 446, 454, 458, 5898, 478, 54582]

/-- The map `x ↦ φ(x) + 1`. -/
def f (x : ℕ) : ℕ := Nat.totient x + 1

/-- For each listed term, A229487(n) is the greatest number converging to prime(n). -/
theorem main : ∀ i : ℕ, i < A229487.length →
    IsGreatest {x : ℕ | 1 ≤ x ∧ ∃ k : ℕ, f^[k] x = Nat.nth Nat.Prime i}
      (A229487.getD i 0) := by
  sorry

end OMA.S_oeis_a039650
