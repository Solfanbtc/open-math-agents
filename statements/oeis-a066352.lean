import Mathlib

/-!
# A066352: Pillai sequence: a(n) is the smallest term in A007924 requiring n primes.

Source: https://oeis.org/A066352
Credit: @Solfanbtc

A007924 writes `n` by the greedy algorithm in the base whose place values are `1` and the primes
(A008578 = `1, 2, 3, 5, 7, ...`): repeatedly subtract the largest place value `≤` the remainder.
Let `g(n)` be the number of places used (the number of "primes", 1 included, in the greedy
representation of `n`). A066352 lists the least `n` with `g(n) = k`: `0, 1, 4, 27, 1354,
401429925999155061`.

Claim (Charles R Greathouse IV, Aug 28 2010, in the entry): on Cramér's conjecture, the number of
primes required is `O(log* n)`, where `log*` is the iterated logarithm (so `a(n)` grows
tetrationally). Stated as: Cramér's conjecture `→ g(n) = O(log* n)` as `n → ∞`.

A python3 check: this greedy count reproduces `a(0), ..., a(4) = 0, 1, 4, 27, 1354`.

Conventions:
* `place m` is the largest element of `{1} ∪ {primes}` that is `≤ m` (`0` for `m = 0`);
  `g n` is the number of greedy steps `m ↦ m - place m` from `n` to `0`.
* Cramér's conjecture, in its usual form: `p_{k+1} - p_k = O((log p_k)²)`, i.e. there is `C` with
  `p_{k+1} - p_k ≤ C (log p_k)²` for all `k` (`p_k = Nat.nth Nat.Prime k`).
* `log* x` is the least `k` with `log^[k] x ≤ 1` (natural logarithm); for `x ≥ 0` it exists.
-/

namespace OMA.S_oeis_a066352

open Asymptotics Filter

/-- The largest place value (`1` or a prime) that is `≤ m`. -/
def place (m : ℕ) : ℕ := Nat.findGreatest (fun q => q = 1 ∨ q.Prime) m

/-- `g n`: the number of places used by the greedy representation of `n` (A007924). -/
noncomputable def g (n : ℕ) : ℕ := sInf {k : ℕ | (fun m => m - place m)^[k] n = 0}

/-- The iterated logarithm `log* x`. -/
noncomputable def logStar (x : ℝ) : ℕ := sInf {k : ℕ | Real.log^[k] x ≤ 1}

/-- Cramér's conjecture: prime gaps are `O((log p)²)`. -/
def CramerConjecture : Prop :=
  ∃ C : ℝ, ∀ k : ℕ, ((Nat.nth Nat.Prime (k + 1) : ℕ) : ℝ) - (Nat.nth Nat.Prime k : ℕ) ≤
    C * Real.log (Nat.nth Nat.Prime k : ℕ) ^ 2

/-- Greathouse's claim: on Cramér's conjecture, `g(n) = O(log* n)`. -/
theorem main : CramerConjecture →
    (fun n : ℕ => (g n : ℝ)) =O[atTop] (fun n : ℕ => (logStar n : ℝ)) := by
  sorry

end OMA.S_oeis_a066352
