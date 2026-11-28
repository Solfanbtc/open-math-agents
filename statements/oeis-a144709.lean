import Mathlib

/-!
# A144709: Integers m > 1 such that there is not a pair of primes (m^2+m-k, m^2+m+k), 1 <= k < m, between successive squares m^2 and (m+1)^2.

Source: https://oeis.org/A144709 (Daniel Tisdale, 2008; name edited by Michel Marcus, 2022;
OEIS Foundation, CC BY-SA 4.0).
Credit: @Solfanbtc

Conjecture (OEIS): the intervals (n^2, (n+1)^2) that do not contain at least one such pair are
sparse as n gets large.

Formalization notes.
* m is a term iff m > 1 and there is no k with 1 ≤ k < m (k ∈ [1, m)) such that m^2 + m - k and m^2 + m + k
  are both prime. For 1 ≤ k < m both numbers lie strictly between m^2 and (m+1)^2, so this is
  exactly the name of the entry.
* "Sparse as n gets large" is read in the standard sense of natural density zero: the
  proportion of terms among 1, ..., N tends to 0. (The entry also reports that the only terms
  up to 2·10^7 are 17, 19, 46, 58, 64, 67, 85, 367, but it conjectures sparseness, not
  finiteness, so finiteness is not stated.)
* A python sieve finds exactly the 8 listed terms among m < 20000.
-/

namespace OMA.S_oeis_a144709

open Filter Topology

/-- `m` is a term of A144709. -/
def IsTerm (m : ℕ) : Prop :=
  1 < m ∧ ¬ ∃ k ∈ Finset.Ico 1 m, (m ^ 2 + m - k).Prime ∧ (m ^ 2 + m + k).Prime

instance (m : ℕ) : Decidable (IsTerm m) := by
  unfold IsTerm; infer_instance

theorem main :
    Tendsto (fun N : ℕ => (((Finset.Icc 1 N).filter IsTerm).card : ℝ) / (N : ℝ))
      atTop (𝓝 0) := by
  sorry

end OMA.S_oeis_a144709
