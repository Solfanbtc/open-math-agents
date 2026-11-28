import Mathlib

/-!
# A005430: Apéry numbers: n*C(2*n,n).

Source: https://oeis.org/A005430
Credit: @Solfanbtc

The source's claim (R. J. Mathar, 2012): the terms of the inverse binomial transform of
A005430 are 2*A132894(n).

Conventions:
* A005430(k) = k * C(2k, k), offset 0.
* The inverse binomial transform of a sequence `a` is `b(n) = Σ_{k=0..n} (-1)^(n-k) C(n,k) a(k)`.
* A132894(n) is taken from its definition (its name on the OEIS): the total number of (1,0)
  steps in all paths of length `n` with steps U = (1,1), D = (1,-1), H = (1,0) that start at
  (0,0) and stay weakly above the x-axis (left factors of Motzkin paths). A path is a function
  `Fin n → Fin 3`, where 0, 1, 2 stand for D, H, U (height change `s - 1`); it stays weakly
  above the axis when every prefix has nonnegative height. Offset 0, so the range is all `n`.
Checked by computation: both sides agree for n ≤ 10 (0, 2, 8, 30, 104, 350, ...), and the
definition gives the data of A132894 (0, 1, 4, 15, 52, 175, ...).
-/

namespace OMA.S_oeis_a005430

/-- A005430(k) = k * C(2k, k). -/
def a (k : ℕ) : ℤ := k * (Nat.choose (2 * k) k : ℤ)

/-- Height change of a step: 0 = D (-1), 1 = H (0), 2 = U (+1). -/
def step (s : Fin 3) : ℤ := (s : ℤ) - 1

/-- The path never goes below the x-axis: every prefix has nonnegative height. -/
def IsLeftFactor {n : ℕ} (p : Fin n → Fin 3) : Prop :=
  ∀ j : Fin (n + 1), 0 ≤ ∑ i : Fin n with i.val < j.val, step (p i)

instance {n : ℕ} (p : Fin n → Fin 3) : Decidable (IsLeftFactor p) := by
  unfold IsLeftFactor; infer_instance

/-- A132894(n): the number of H steps in all left factors of Motzkin paths of length `n`. -/
def A132894 (n : ℕ) : ℕ :=
  ∑ p ∈ (Finset.univ : Finset (Fin n → Fin 3)).filter IsLeftFactor,
    ((Finset.univ : Finset (Fin n)).filter (fun i => p i = 1)).card

theorem main : ∀ n : ℕ,
    ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - k) * (Nat.choose n k : ℤ) * a k =
      2 * (A132894 n : ℤ) := by
  sorry

end OMA.S_oeis_a005430
