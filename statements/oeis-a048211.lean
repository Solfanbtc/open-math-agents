import Mathlib

/-!
# A048211: Number of distinct resistances that can be produced from a circuit of n equal resistors using only series and parallel combination

Source: https://oeis.org/A048211
Credit: @Solfanbtc

Conjecture (OEIS A048211, formula section, Bill McEachen, Jun 08 2024):
a(n) ~ K * a(n-1), K approx 2.54.

Here a(n) is the number of distinct resistances obtained from exactly n equal (1 ohm)
resistors using only series and parallel combinations. As in the Maple and PARI programs of
the entry, `resistances 1 = {1}` and for n >= 2 the set `resistances n` collects `f + g`
(series) and `f * g / (f + g)` (parallel) for `f ∈ resistances i`, `g ∈ resistances (n - i)`,
1 <= i < n. (Evaluated in Python, the cardinalities for n = 1..14 are
1, 2, 4, 9, 22, 53, 131, 337, 869, 2213, 5691, 14517, 37017, 93731, matching the data.)

The claim `a(n) ~ K * a(n-1)` means that the ratio a(n+1)/a(n) converges to a constant K,
which is what is stated. The value of K is given only as approximately 2.54 (the ratio of the
last two listed terms is about 2.544); this numerical estimate is not a precise statement
and is not part of the formal claim.

The bounds (2.414^n)/4 < a(n) < (1-1/n)*(0.318)*(2.618^n) for n > 3 quoted in the same
formula line are attributed to Khan and are not the conjecture of this entry.
-/

namespace OMA.S_oeis_a048211

/-- The set of resistances realizable with exactly `n` unit resistors combined in series
and in parallel. -/
def resistances : ℕ → Finset ℚ
  | 0 => ∅
  | 1 => {1}
  | n + 2 => (Finset.univ : Finset (Fin (n + 1))).biUnion fun i =>
      have : (i : ℕ) + 1 < n + 2 := by omega
      have : n + 1 - i < n + 2 := by omega
      (resistances ((i : ℕ) + 1) ×ˢ resistances (n + 1 - i)).biUnion fun fg =>
        {fg.1 + fg.2, fg.1 * fg.2 / (fg.1 + fg.2)}

/-- A048211(n): the number of distinct such resistances. -/
def a (n : ℕ) : ℕ := (resistances n).card

/-- Conjecture: `a (n + 1) / a n` converges to a constant `K` (numerically about 2.54). -/
theorem main : ∃ K : ℝ,
    Filter.Tendsto (fun n : ℕ => (a (n + 1) : ℝ) / a n) Filter.atTop (nhds K) := by
  sorry

end OMA.S_oeis_a048211
