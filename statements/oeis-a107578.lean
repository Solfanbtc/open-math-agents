import Mathlib

/-!
# A107578: Prime index of A000101(n), maximal gap upper end prime index.

Source: https://oeis.org/A107578
Credit: @Solfanbtc

Conjecture (Alexei Kourbatov, Jan 18 2019, in the entry): log a(n) ~ n/2, i.e. record prime
gaps occur about twice as often as records in an i.i.d. random sequence of comparable length.

Conventions.
* p_m = `Nat.nth Nat.Prime m` (0-indexed: p_0 = 2), gap g_m = p_(m+1) - p_m. Index m is a
  record (maximal gap) if g_j < g_m for all j < m (same notion as `IsMaximalPrimeGapIndex` in
  FormalConjectures/Wikipedia/MaximalPrimeGap.lean). The record gaps' upper ends are A000101
  (3, 5, 11, 29, 97, ...), and the upper end of the record at m is p_(m+1), whose 1-indexed
  prime index (A000720) is m + 2. With e(k) the k-th record index (0-indexed),
  a(n) = e(n-1) + 2 for n ≥ 1 (offset 1): a = 2, 3, 5, 10, 25, 31, 100, ... (the data).
* "log a(n) ~ n/2" is stated as log a(n) / (n/2) → 1 as n → ∞.
-/

namespace OMA.S_oeis_a107578

/-- The m-th prime gap p_(m+1) - p_m (0-indexed primes). -/
noncomputable def gap (m : ℕ) : ℕ := Nat.nth Nat.Prime (m + 1) - Nat.nth Nat.Prime m

/-- m is a record (maximal prime gap) index. -/
def IsRecord (m : ℕ) : Prop := ∀ j : ℕ, j < m → gap j < gap m

/-- A107578 (offset 1): prime index of the upper end of the n-th record gap. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsRecord (n - 1) + 2

theorem main :
    Filter.Tendsto (fun n : ℕ => Real.log (a n) / ((n : ℝ) / 2)) Filter.atTop (nhds 1) := by
  sorry

end OMA.S_oeis_a107578
