import Mathlib

/-!
# A093963: Antidiagonal sums of array in A093966.

Source: https://oeis.org/A093963
Credit: @Solfanbtc

A093966 is the array of the numbers of `n`-long `k`-ary words that simultaneously avoid the
patterns `112` and `221` (Burstein–Mansour). A word `w` contains `112` if there are positions
`i < j < l` with `w i = w j < w l`, and contains `221` if `w i = w j > w l`; so it avoids both
iff there are no `i < j < l` with `w i = w j ≠ w l`.

`a(n)` (offset 1) is the `n`-th antidiagonal sum: `a(n) = ∑_{k=1}^{n} W(k, n+1-k)`, where
`W(k, m)` is the number of such words of length `m` over a `k`-letter alphabet. (The sum over an
antidiagonal does not depend on which index is the row.)

Conjecture (R. J. Mathar, Nov 10 2013, %F of A093963): for `n ≥ 7` (so that `a(n-6)` is defined),
`2a(n) - 5a(n-1) - (n+2)a(n-2) + 2(n+6)a(n-3) + (n-13)a(n-4) - 4(n-3)a(n-5) + 2(n-3)a(n-6) = 0`.

Checked with python3: brute-force counting gives `a(1..8) = 1, 3, 8, 20, 49, 123, 312, 824`, and
the recurrence holds on all 27 listed terms (%S, %T, %U), i.e. for `7 ≤ n ≤ 27`.
-/

namespace OMA.S_oeis_a093963

/-- The word `w` (of length `m` over `Fin k`) avoids both `112` and `221`. -/
def Avoids {m k : ℕ} (w : Fin m → Fin k) : Prop :=
  ¬ ∃ i j l : Fin m, i < j ∧ j < l ∧ w i = w j ∧ w j ≠ w l

instance {m k : ℕ} (w : Fin m → Fin k) : Decidable (Avoids w) := by
  unfold Avoids; infer_instance

/-- `W k m`: number of `m`-long `k`-ary words avoiding `112` and `221` (array A093966). -/
def W (k m : ℕ) : ℕ :=
  (Finset.univ.filter (fun w : Fin m → Fin k => Avoids w)).card

/-- A093963: antidiagonal sums of A093966. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 n, W k (n + 1 - k)

/-- Mathar's conjectured holonomic recurrence. -/
theorem main : ∀ n : ℕ, 7 ≤ n →
    2 * (a n : ℤ) - 5 * a (n - 1) - ((n : ℤ) + 2) * a (n - 2) + 2 * ((n : ℤ) + 6) * a (n - 3)
      + ((n : ℤ) - 13) * a (n - 4) - 4 * ((n : ℤ) - 3) * a (n - 5)
      + 2 * ((n : ℤ) - 3) * a (n - 6) = 0 := by
  sorry

end OMA.S_oeis_a093963
