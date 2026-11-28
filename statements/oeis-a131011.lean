import Mathlib

/-!
# A131011: a(n) = A121295(n) - A121263(n).

Source: https://oeis.org/A131011
Credit: @Solfanbtc

Claim (entry comment, N. J. A. Sloane): all terms are ≥ 0 (offset 10, so for every n ≥ 10).
Reference: D. Applegate, M. LeBrun, N. J. A. Sloane, "Descending Dungeons and Iterated
Base-Changing", arXiv:math/0611293.

Definitions (from A121263 and A121295). `N_b`, "N read in base b", takes the decimal digits
of `N` and evaluates them as a base-`b` expansion: `Nat.ofDigits b (Nat.digits 10 N)`.
* A121263 (alpha): alpha(n) = 10_(11_(12_(⋯_((n-1)_n)))), subscripts evaluated from the bottom up;
  alpha(10) = 10.
* A121295 (gamma): gamma(10) = 10 and gamma(n) = n_(gamma(n-1)) for n > 10, i.e.
  gamma(n) = n_((n-1)_(⋯_(11_10))).
a(n) = gamma(n) - alpha(n) is taken in ℤ, so the claim is that it is ≥ 0 for every n ≥ 10.
These definitions reproduce all 34 listed terms 0, …, 0, 45, 134, …, 697843906028
(n = 10..43), checked in python with the same recursions.
-/

namespace OMA.S_oeis_a131011

/-- `N` read in base `b`: its decimal digits evaluated as a base-`b` expansion. -/
def readIn (N b : ℕ) : ℕ := Nat.ofDigits b (Nat.digits 10 N)

/-- A121263(n) for n ≥ 10: 10_(11_(⋯_((n-1)_n))). -/
def alpha (n : ℕ) : ℕ := (List.range' 10 (n - 10)).foldr (fun i acc => readIn i acc) n

/-- A121295(n) for n ≥ 10: gamma(10) = 10, gamma(n) = n read in base gamma(n-1). -/
def gamma (n : ℕ) : ℕ := (List.range' 11 (n - 10)).foldl (fun acc i => readIn i acc) 10

/-- A131011(n) = A121295(n) - A121263(n), for n ≥ 10. -/
def a (n : ℕ) : ℤ := (gamma n : ℤ) - alpha n

theorem main : ∀ n : ℕ, 10 ≤ n → 0 ≤ a n := by
  sorry

end OMA.S_oeis_a131011
