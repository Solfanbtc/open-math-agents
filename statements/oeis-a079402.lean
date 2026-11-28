import Mathlib

/-!
# A079402: Permutations of n^2 integers free of monotone (n+1)-subsequences.

Source: https://oeis.org/A079402
Credit: @Solfanbtc

Conjecture (Joseph Myers, Jan 04 2003, in the entry): the number of permutations of n^2
distinct integers free of any monotonic increasing or decreasing (n+1)-subsequence equals
((n^2)! * Product_{k=0..n-1} k!/(n+k)!)^2 (the entry's formula; data 1, 1, 4, 1764,
577152576, ...).

Status: confirmed (Claude Lenormand, per the entry); it follows from the Robinson-Schensted
correspondence (such permutations correspond to pairs of standard Young tableaux of square
shape n × n, Meeussen's comment) and the hook length formula, whose count is
(n^2)! ∏_{k<n} k!/(n+k)!.

Conventions.
* Permutations of n^2 distinct integers are identified with σ ∈ `Equiv.Perm (Fin (n*n))`
  (only the relative order matters). A monotonic (n+1)-subsequence is given by positions
  f : Fin (n+1) ↪o Fin (n*n) (increasing) with σ ∘ f strictly increasing or strictly
  decreasing.
* The formula is evaluated in ℚ (it is an integer).
-/

namespace OMA.S_oeis_a079402

/-- σ has a monotone (increasing or decreasing) subsequence of length m. -/
def HasMonotone {N : ℕ} (σ : Equiv.Perm (Fin N)) (m : ℕ) : Prop :=
  ∃ f : Fin m ↪o Fin N, StrictMono (fun i => σ (f i)) ∨ StrictAnti (fun i => σ (f i))

theorem main : ∀ n : ℕ,
    (Nat.card {σ : Equiv.Perm (Fin (n * n)) // ¬ HasMonotone σ (n + 1)} : ℚ) =
      (((n * n).factorial : ℚ) *
        ∏ k ∈ Finset.range n, ((k.factorial : ℚ) / ((n + k).factorial : ℚ))) ^ 2 := by
  sorry

end OMA.S_oeis_a079402
