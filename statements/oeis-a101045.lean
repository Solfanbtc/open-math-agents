import Mathlib

/-!
# A101045: Record size primes in A101044.

Source: https://oeis.org/A101045
Credit: @Solfanbtc

Conjecture (Ya-Ping Lu, Sep 24 2020): lim_{n->infinity} a(n)/n^2 = 1.

Definitions.
* A020483(m) (offset 0) is the least prime `p` such that `p + 2m` is also prime; here
  `f m = sInf {p | p prime ∧ p + 2m prime}`.
* A101044 lists the primes in order of first appearance in A020483 (with 2 first), so its
  record values are the record values of `m ↦ f m` (m = 0, 1, 2, ...); this is also exactly the
  program given in the entry (Ya-Ping Lu): run m = 0, 1, 2, ... and print `f m` whenever it
  exceeds all earlier values.
* `IsRecord p` : `p = f m` for some `m` with `f m' < p` for all `m' < m`. If some `f m'` were
  undefined (`sInf ∅ = 0`), it would not affect records, matching the program.
* `a n = Nat.nth IsRecord (n - 1)`, offset 1: records are strictly increasing in `m`, so this
  lists them in order. (python3: the records for m < 10^6 are the first 24 data terms
  2, 3, 5, 7, 13, ..., 619.)
-/

namespace OMA.S_oeis_a101045

/-- A020483(m): the least prime `p` with `p + 2m` prime. -/
noncomputable def f (m : ℕ) : ℕ := sInf {p : ℕ | p.Prime ∧ (p + 2 * m).Prime}

/-- `p` is a record value of `f`. -/
def IsRecord (p : ℕ) : Prop := ∃ m : ℕ, f m = p ∧ ∀ m' < m, f m' < p

/-- A101045(n), offset 1. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsRecord (n - 1)

theorem main :
    Filter.Tendsto (fun n : ℕ => (a n : ℝ) / (n : ℝ) ^ 2) Filter.atTop (nhds 1) := by
  sorry

end OMA.S_oeis_a101045
