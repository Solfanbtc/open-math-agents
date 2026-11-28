import Mathlib

/-!
# A054763: Residues of consecutive prime differences modulo 6.

Source: https://oeis.org/A054763
Credit: @Solfanbtc

a(n) = (prime(n+1) - prime(n)) mod 6. Conjecture (in the entry): the percentage of zeros in
A054763 asymptotically runs to 50%.

Conventions.
* p_m = `Nat.nth Nat.Prime m` (0-indexed: p_0 = 2); the m-th term (0-indexed here) is
  (p_(m+1) - p_m) mod 6. The index shift does not affect the asymptotic proportion.
* "The percentage of zeros asymptotically runs to 50%" is stated as
  #{m < N : (p_(m+1) - p_m) ≡ 0 (mod 6)} / N → 1/2 as N → ∞.
-/

namespace OMA.S_oeis_a054763

/-- Number of m < N with 6 ∣ p_(m+1) - p_m. -/
noncomputable def zeroCount (N : ℕ) : ℕ :=
  ((Finset.range N).filter fun m => (Nat.nth Nat.Prime (m + 1) - Nat.nth Nat.Prime m) % 6 = 0).card

theorem main :
    Filter.Tendsto (fun N : ℕ => (zeroCount N : ℝ) / N) Filter.atTop (nhds (1 / 2)) := by
  sorry

end OMA.S_oeis_a054763
