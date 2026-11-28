import Mathlib

/-!
# A087357: Index of powers of 2 arising as the difference of a pair of successive terms of A087356.

Source: https://oeis.org/A087357
Credit: @Solfanbtc

A087356: `b(0) = 2` and `b(k)` is the smallest prime of the form `b(k-1) + 2^r` with `r` not
used by an earlier difference (smallest prime ⇔ smallest such `r`); the sequence stops if no
such prime exists. A087357 (offset 0) lists the exponents `r` in order:
`b(k+1) - b(k) = 2^(A087357(k))`. We checked by computer that this rule reproduces
b(0..16) of A087356 and the exponents 0, 1, 3, 2, 13, 6, 11, 4, 5, 10, 35, 16, 25, 26, 19, 12.

Below, `state k = some (b(k), {exponents used so far})`, or `none` once the sequence stopped.

Conjecture (Amarnath Murthy, 2003): every natural number is a member of A087357, i.e.
the sequence never stops and every exponent `r` is eventually used.
-/

namespace OMA.S_oeis_a087357

/-- The exponents available from the prime `p` when `used` are already used. -/
def cands (p : ℕ) (used : Finset ℕ) : Set ℕ := {r | r ∉ used ∧ (p + 2 ^ r).Prime}

/-- After `k` steps: `some (b(k), exponents used)`, or `none` if the sequence has stopped. -/
noncomputable def state : ℕ → Option (ℕ × Finset ℕ)
  | 0 => some (2, ∅)
  | k + 1 =>
      match state k with
      | none => none
      | some (p, used) =>
          haveI := Classical.dec (cands p used).Nonempty
          if (cands p used).Nonempty then
            some (p + 2 ^ sInf (cands p used), insert (sInf (cands p used)) used)
          else none

/-- Every natural number `r` occurs in A087357. -/
theorem main : ∀ r : ℕ, ∃ k : ℕ, ∃ p : ℕ, ∃ used : Finset ℕ,
    state k = some (p, used) ∧ r ∈ used := by
  sorry

end OMA.S_oeis_a087357
