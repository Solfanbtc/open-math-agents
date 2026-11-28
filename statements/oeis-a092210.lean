import Mathlib

/-!
# A092210: Positive integers n such that the trajectory of n under the Reverse and Add! operation carried out in base 2 (presumably) does not join the trajectory of any m < n.

Source: https://oeis.org/A092210
Credit: @Solfanbtc

The base-2 Reverse and Add! operation is `R(n) = n + rev₂(n)`, where `rev₂(n)` is the number
whose binary digits are those of `n` reversed. The trajectory of `n` is `n, R(n), R(R(n)), ...`;
two trajectories join when they have a common value.

The entry's conjecture (Klaus Brockhaus): the base-2 trajectories of the listed terms do not
join, i.e. for any two distinct terms among all 46 terms of %S, %T, %U the trajectories are
disjoint. (The entry has checked this for 1000 steps, and for 5000 steps on pairs from
1, 16, 64, 74, 98, 107.) Joining is an equivalence relation, so this says exactly that the
listed numbers lie in pairwise distinct classes. Checked by computer: with a 1000-step
cutoff, the greedy computation of the definition reproduces exactly these 46 terms
below 4190.
-/

namespace OMA.S_oeis_a092210

/-- Reverse the binary digits of `n`. -/
def rev2 (n : ℕ) : ℕ := Nat.ofDigits 2 (Nat.digits 2 n).reverse

/-- One step of the base-2 Reverse and Add! operation. -/
def R (n : ℕ) : ℕ := n + rev2 n

/-- The listed terms of A092210 (%S, %T, %U). -/
def terms : List ℕ :=
  [1, 16, 64, 74, 98, 107, 259, 266, 271, 275, 298, 398, 442, 454, 522, 794, 911, 1027,
   1046, 1057, 1066, 1070, 1073, 1076, 1081, 1082, 1085, 1115, 1274, 1422, 1562,
   1570, 1967, 2070, 2329, 3106, 3355, 3871, 4099, 4114, 4120, 4126, 4136, 4152, 4182, 4189]

/-- The trajectories of distinct listed terms never join. -/
theorem main :
    ∀ a ∈ terms, ∀ b ∈ terms, a ≠ b → ∀ i j : ℕ, R^[i] a ≠ R^[j] b := by
  sorry

end OMA.S_oeis_a092210
