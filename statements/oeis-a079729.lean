import Mathlib

/-!
# A079729: Kolakoski-(1,2,3) sequence: a(n) is the length of the n-th run.

Source: https://oeis.org/A079729
Credit: @Solfanbtc

Conjecture (Michel Dekking, Jan 31 2018, OEIS A079729): the frequencies of 1's, 2's and 3's in
(a(n)) exist and are all equal to 1/3.

Definition (offset 1): the sequence over the alphabet 1, 2, 3 whose runs carry the symbols
1, 2, 3, 1, 2, 3, ... in turn and whose n-th run has length a(n), starting 1, 2, 2, ... It is
generated run by run: run number r (from 0) has symbol r mod 3 + 1 and length equal to the
r-th term (0-based) if already generated, otherwise equal to its own symbol (this only happens for
r = 1, giving the start 1, 2, 2). `runs r` is the list after r runs; it has length >= r, and
a(m) is its (m-1)-th entry with r = m. Frequency of v: #{m <= N : a(m) = v} / N.
Checked numerically: reproduces the listed terms; the frequencies over the first 3 * 10^6 terms
are 0.333358, 0.333347, 0.333294.
-/

namespace OMA.S_oeis_a079729

open Filter

/-- The sequence after `r` runs. -/
def runs : ℕ → List ℕ
  | 0 => []
  | r + 1 =>
    let l := runs r
    let c := r % 3 + 1
    l ++ List.replicate (if r < l.length then l.getD r 0 else c) c

/-- a(m), for m ≥ 1. -/
def a (m : ℕ) : ℕ := (runs m).getD (m - 1) 0

theorem main : ∀ v ∈ ({1, 2, 3} : Finset ℕ),
    Tendsto (fun N : ℕ => (((Finset.Icc 1 N).filter fun m => a m = v).card : ℝ) / N) atTop
      (nhds (1 / 3)) := by
  sorry

end OMA.S_oeis_a079729
