import Mathlib

/-!
# A059269: Numbers m for which the number of divisors, tau(m), is divisible by 3.

Source: https://oeis.org/A059269
Credit: @Solfanbtc

Conjecture (Charles R Greathouse IV, 2012): `a(n) ~ k n` with
`k = 1/(1 - ∏_p ∏_{i ≥ 1} (1 - (p-1)/p^(3i))) = 3.743455…`.

The entry records (Amiram Eldar, 2020) that the asymptotic density of the sequence is
`1 - ζ(3)/ζ(2) = 1 - 6 ζ(3)/π² = 0.2692370305…` (Sathe, 1945), so `a(n) ~ k n` is true but with
`k = 1/(1 - 6 ζ(3)/π²) = 3.7141993349…`, not 3.743455…: the conjecture as written (with that
constant) is false. The minimal fix, which is the entry's own corrected claim, is stated here:
the sequence has natural density `1 - 6 ζ(3)/π²` (equivalent to `a(n) ~ n / (1 - 6 ζ(3)/π²)`).
This is a known result (L. G. Sathe, 1945).

Checked with python3: the terms below 50 match the data, and the proportion of `m ≤ 300000`
with `3 ∣ τ(m)` is 0.26917.
-/

namespace OMA.S_oeis_a059269

open Filter Topology

/-- The number of `m ≤ N`, `m ≥ 1`, whose number of divisors is divisible by 3. -/
def count (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (fun m => 3 ∣ m.divisors.card)).card

/-- A059269 has natural density `1 - 6 ζ(3)/π²`. -/
theorem main :
    Tendsto (fun N : ℕ => (count N : ℝ) / N) atTop
      (𝓝 (1 - 6 * (riemannZeta 3).re / Real.pi ^ 2)) := by
  sorry

end OMA.S_oeis_a059269
