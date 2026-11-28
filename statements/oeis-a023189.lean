import Mathlib

/-!
# A023189: Conjecturally, number of infinitely recurring prime patterns of width 2n-1.

Source: https://oeis.org/A023189
Credit: @Solfanbtc

A prime pattern of width `w` is a word in `{p, c}` of length `w` (prime / composite); it recurs
infinitely often if infinitely many windows `m, m+1, ..., m+w-1` of consecutive integers have
exactly this pattern of primes. A023189 counts the infinitely recurring patterns of width `2n - 1`
that start and end with a prime (Sean A. Irvine; e.g. width 7: `pcccccp, pcpcccp, pcccpcp`):
`1, 1, 1, 3, 4, 4, 14, 13, 16, 48, 55, ...`. The word "Conjecturally" in the name refers to the
fact that these values are obtained from the admissibility criterion: a pattern with prime
positions `H` is expected (by the prime k-tuple conjecture) to recur infinitely often iff `H` is
admissible, i.e. `H` misses some residue class modulo every prime.

Conjecture stated here: for every `n ≥ 1`, the number of infinitely recurring prime patterns of
width `2n - 1` starting and ending with a prime equals the number of admissible sets
`H ⊆ {0, ..., 2n - 2}` with `0, 2n - 2 ∈ H` (the values listed in the entry).

A python3 check: the admissible count reproduces the data for `n = 1, ..., 11`.

Conventions:
* A pattern is the set `H ⊆ {0, ..., w - 1}` of its prime positions; a window starting at `m`
  has pattern `H` iff for all `i < w`, `m + i` is prime exactly when `i ∈ H`. (Positions not in
  `H` are then non-prime; for large `m` these are composite.)
* Admissible: for every prime `q` some `r < q` has `q ∤ r + h` for all `h ∈ H`.
-/

namespace OMA.S_oeis_a023189

/-- `H` is admissible. -/
def Admissible (H : Finset ℕ) : Prop := ∀ q : ℕ, q.Prime → ∃ r < q, ∀ h ∈ H, ¬ q ∣ r + h

/-- The pattern with prime positions `H` (width `w`) occurs infinitely often. -/
def Recurs (w : ℕ) (H : Finset ℕ) : Prop :=
  Set.Infinite {m : ℕ | ∀ i < w, ((m + i).Prime ↔ i ∈ H)}

/-- Patterns of width `w` starting and ending with a prime. -/
def EndsPrime (w : ℕ) (H : Finset ℕ) : Prop := H ⊆ Finset.range w ∧ 0 ∈ H ∧ w - 1 ∈ H

/-- The number of infinitely recurring prime patterns of width `2n - 1` starting and ending with a
prime equals the number of admissible such patterns. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    {H : Finset ℕ | EndsPrime (2 * n - 1) H ∧ Recurs (2 * n - 1) H}.ncard =
      {H : Finset ℕ | EndsPrime (2 * n - 1) H ∧ Admissible H}.ncard := by
  sorry

end OMA.S_oeis_a023189
