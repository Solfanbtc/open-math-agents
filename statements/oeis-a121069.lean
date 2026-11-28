import Mathlib

/-!
# A121069: Conjectured sequence for jumping champions greater than 1 (most common prime gaps up to x, for some x).

Source: https://oeis.org/A121069
Credit: @Solfanbtc

Conjecture (OEIS A121069, %N and %F "Consists of 4 and the primorials (A002110)"; the jumping
champion conjecture of Odlyzko, Rubinstein and Wolf, Jumping champions, Experiment. Math. 8
(1999)): the jumping champions greater than 1 are exactly 4 and the primorials
2, 6, 30, 210, 2310, ... It is open unconditionally.

Conventions:
* `gapCount x d` is the number of pairs of consecutive primes `p < p'` with `p' ≤ x` and
  `p' - p = d` (for `d > 0`): `p` and `p + d` are prime, `p + d ≤ x`, and no prime lies strictly
  between them.
* `d` is a jumping champion if for some `x` it is a most common gap between consecutive primes
  up to `x`: `gapCount x d ≥ gapCount x d'` for every `d'`. Ties count (each tied gap is a
  champion). We also require `gapCount x d > 0`: otherwise for `x ≤ 2`, where no gap occurs at
  all, every `d` would trivially be a "most common" gap; this is the minimal fix.
* The primorials greater than 1 are `primorial n` (product of the primes `≤ n`) for `n ≥ 2`,
  i.e. the values 2, 6, 30, ...; `d > 1` excludes the champion 1 (x = 3, gap 3 - 2).
* Checked in Python: for x ≤ 2·10^6 the champions are exactly 1, 2, 4, 6 (6 ties for some small
  x), consistent with the conjecture.
-/

namespace OMA.S_oeis_a121069

/-- Number of gaps equal to `d` between consecutive primes `p < p' ≤ x`. -/
def gapCount (x d : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter fun p =>
    0 < d ∧ p.Prime ∧ (p + d).Prime ∧ p + d ≤ x ∧ ∀ q ∈ Finset.Ioo p (p + d), ¬ q.Prime).card

/-- `d` is a jumping champion: for some `x`, a most common gap between consecutive primes
up to `x`. -/
def IsJumpingChampion (d : ℕ) : Prop :=
  ∃ x : ℕ, 0 < gapCount x d ∧ ∀ d' : ℕ, gapCount x d' ≤ gapCount x d

/-- The jumping champions greater than 1 are exactly 4 and the primorials. -/
theorem main :
    ∀ d : ℕ, 1 < d → (IsJumpingChampion d ↔ d = 4 ∨ ∃ n : ℕ, 2 ≤ n ∧ d = primorial n) := by
  sorry

end OMA.S_oeis_a121069
