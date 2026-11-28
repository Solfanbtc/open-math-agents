import Mathlib

/-!
# A089588: a(n) = A089587(2^n+1) for n >= 0.

Source: https://oeis.org/A089588
Credit: @Solfanbtc

A089587(n), for `n > 2`, is the smallest `k` with `0 < k < n` maximizing the number of descents
`#{m : 1 ≤ m ≤ n - 1, (k^m mod n) > (k^(m+1) mod n)}`. (For example A089587(7) = 4, with 4
descents.) Checked with python3: this reproduces the 79 listed terms of A089587 (with
A089587(1) = 0, A089587(2) = 1) and the data of A089588.

Conjectures (P. D. Hanna): A089587(2^(2^j) + 1) = 2 for `j ≥ 0` (A089587 %F), and "it is
conjectured that A089587(n) = 2 only when n is a Fermat number 2^(2^j) + 1" (comment in both
entries). Together, for `n > 2`: A089587(n) = 2 iff `n` is a Fermat number. `main` states this.
The %F line of A089588, "a(2^k+1) = 2 for k >= 0", is mis-indexed: read in A089588's indexing it
gives A089588(3) = A089587(9) = 7. The intended claim is A089588(2^k) = A089587(2^(2^k)+1) = 2,
the first half above. (python3: the equivalence holds for `3 ≤ n < 700`, and A089587(257) = 2.)
-/

namespace OMA.S_oeis_a089588

/-- Number of descents of the power residues `k^m mod n`, `m = 1, …, n - 1`. -/
def descents (n k : ℕ) : ℕ :=
  ((Finset.Icc 1 (n - 1)).filter (fun m => k ^ (m + 1) % n < k ^ m % n)).card

/-- A089587(n) for `n > 2`: the least `k ∈ (0, n)` with the maximal number of descents. -/
noncomputable def A089587 (n : ℕ) : ℕ :=
  sInf {k | 0 < k ∧ k < n ∧ ∀ j, 0 < j → j < n → descents n j ≤ descents n k}

theorem main : ∀ n : ℕ, 2 < n → (A089587 n = 2 ↔ ∃ j : ℕ, n = 2 ^ 2 ^ j + 1) := by
  sorry

end OMA.S_oeis_a089588
