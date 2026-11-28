import Mathlib

/-!
# A086554: a(1) = 1; for n>1, a(n) = smallest number not included earlier such that each P+1 is prime, where P is the product of an (n-1)-set from the previous n terms.

Source: https://oeis.org/A086554
Credit: @Solfanbtc

For `n > 1`, `a(n)` must make `P + 1` prime for every product `P` of `n - 1` of the `n` terms
`a(1), ..., a(n)` (example: a(4) = 23 since 1·2·6+1, 2·6·23+1, 1·6·23+1, 1·2·23+1 are prime).
The data (1, 2, 6, 23, 370, 1056, 36695, 491942, 23005823) is increasing and is reproduced by
taking for `a(n)` the smallest number GREATER than `a(n-1)` with this property, which we
checked by computer for a(1..7). Read literally ("smallest number not included earlier"),
the definition would instead give a(4) = 3 (1·2·6+1 = 13, 2·6·3+1 = 37, 1·6·3+1 = 19,
1·2·3+1 = 7 are all prime), contradicting the data; so we use the reading that matches the
data, which is the sequence the conjecture is about. The sequence stops when no such number
exists.

Below, `state k = some [a(1), ..., a(k+1)]`, or `none` once the sequence has stopped.

Conjecture (Amarnath Murthy, 2003): the sequence is finite (no more terms below 166890000,
D. Wasserman).
-/

namespace OMA.S_oeis_a086554

/-- The admissible next terms after the (increasing, nonempty) list of terms `l`. -/
def cands (l : List ℕ) : Set ℕ :=
  {x | l.getLastD 0 < x ∧ ∀ T ⊆ insert x l.toFinset, T.card = l.length → (T.prod id + 1).Prime}

/-- `some [a(1), ..., a(k+1)]`, or `none` if the sequence has fewer than `k + 1` terms. -/
noncomputable def state : ℕ → Option (List ℕ)
  | 0 => some [1]
  | k + 1 =>
      match state k with
      | none => none
      | some l =>
          haveI := Classical.dec (cands l).Nonempty
          if (cands l).Nonempty then some (l ++ [sInf (cands l)]) else none

/-- A086554 is finite. -/
theorem main : ∃ k : ℕ, state k = none := by
  sorry

end OMA.S_oeis_a086554
