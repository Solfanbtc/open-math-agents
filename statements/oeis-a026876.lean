import Mathlib

/-!
# A026876: T(2n+1, n+1), T given by A026758.

Source: https://oeis.org/A026876
Credit: @Solfanbtc

Two conjectures of Michael D. Weiner (Aug 04 2018, in the entry):
1. The invert transform of this sequence (shifted) appears to be A165538 (number of
   permutations of length n avoiding the patterns 4312 and 3142).
2. The g.f. f satisfies x^6 f^4 + x^3 (4x-1)(x-1) f^3 + x (x-1)(6x^2-6x+1) f^2
   + (4x-1)(x-1)^2 f + (x-1)^2 = 0.
`main` is their conjunction.

Conventions.
* T = A026758 by its defining recurrence (name of A026758): T(n,0) = T(n,n) = 1; for n ≥ 2 and
  1 ≤ k ≤ n-1, T(n,k) = T(n-1,k-1) + T(n-2,k-1) + T(n-1,k) if n is odd and k ≤ (n-1)/2, else
  T(n,k) = T(n-1,k-1) + T(n-1,k). (The path description in A026758 gives the mirror image
  T(n, n-k), so the recurrence, which matches A026758's displayed rows, is used.)
  a(n) = T(2n+1, n+1), offset 0: 1, 3, 11, 43, 174, ... (python3: all 24 listed terms).
* "Invert transform ... (shifted)": the invert transform of (b_1, b_2, ...) is (c_n) with
  1 + Σ_{n≥1} c_n x^n = 1/(1 - Σ_{n≥1} b_n x^n). With the sequence shifted to
  b_1 = 1, b_{n+2} = a(n) (i.e. prepending 1), python3 gives c = 1, 2, 6, 22, 88, 367, ...
  = A165538(1, 2, ...), with c_0 = 1 = A165538(0); without the shift it gives 1, 4, 18, ...,
  and with the other shift (prepending 0) 0, 1, 3, 12, ..., neither of which fits. So the claim
  is stated as (Σ_n A165538(n) x^n) * (1 - x (1 + Σ_n a(n) x^(n+1))) = 1.
* A165538(n) = number of σ ∈ S_n containing neither 4312 nor 3142 (0-indexed one-line
  patterns [3,2,0,1] and [2,0,3,1]); a permutation contains pattern p if some 4 positions
  i0 < i1 < i2 < i3 have values in the same relative order as p. Brute force (python3) gives
  1, 1, 2, 6, 22, 88, 367, 1568, 6810 for n = 0..8, matching A165538.
* Conjecture 2 is checked on the coefficients of x^0..x^29 (python3).
-/

namespace OMA.S_oeis_a026876

/-- The triangle A026758 (0 for k > n). -/
def T : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | 1, k => if k ≤ 1 then 1 else 0
  | n + 2, k =>
    if n + 2 < k then 0
    else if k = 0 ∨ k = n + 2 then 1
    else if (n + 2) % 2 = 1 ∧ k ≤ (n + 1) / 2 then T (n + 1) (k - 1) + T n (k - 1) + T (n + 1) k
    else T (n + 1) (k - 1) + T (n + 1) k

/-- A026876. -/
def a (n : ℕ) : ℕ := T (2 * n + 1) (n + 1)

/-- σ contains the pattern `p` (given by its one-line values on `Fin 4`). -/
def Contains {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Fin 4 → ℕ) : Prop :=
  ∃ f : Fin 4 ↪o Fin n, ∀ i j : Fin 4, σ (f i) < σ (f j) ↔ p i < p j

/-- A165538: permutations of length n avoiding 4312 and 3142. -/
noncomputable def A165538 (n : ℕ) : ℕ :=
  Nat.card {σ : Equiv.Perm (Fin n) // ¬ Contains σ ![3, 2, 0, 1] ∧ ¬ Contains σ ![2, 0, 3, 1]}

open PowerSeries in
theorem main :
    (PowerSeries.mk (fun n => (A165538 n : ℤ)) *
        (1 - X * PowerSeries.mk (fun n => if n = 0 then (1 : ℤ) else (a (n - 1) : ℤ))) = 1) ∧
    (let f : PowerSeries ℤ := PowerSeries.mk fun n => (a n : ℤ)
     X ^ 6 * f ^ 4 + X ^ 3 * (4 * X - 1) * (X - 1) * f ^ 3
       + X * (X - 1) * (6 * X ^ 2 - 6 * X + 1) * f ^ 2
       + (4 * X - 1) * (X - 1) ^ 2 * f + (X - 1) ^ 2 = 0) := by
  sorry

end OMA.S_oeis_a026876
