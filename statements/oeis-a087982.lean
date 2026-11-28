import Mathlib

/-!
# A087982: Maximal permanent of a nonsingular n X n (+1,-1)-matrix.

Source: https://oeis.org/A087982
Credit: @Solfanbtc

Conjecture (Kräuter and Seifter, recorded in the comments of A087982): for n ≥ 5 the maximal
permanent of a nonsingular n × n (+1,-1)-matrix is attained by a matrix with exactly n - 1
entries -1 on the diagonal. As A087981 (referenced there) makes precise, this matrix has
exactly n - 1 entries -1, all on the diagonal, and +1 everywhere else; its permanent is
A087981(n - 1). (The OEIS entry notes it was proved by Budrevich and Guterman,
arXiv:1810.04439.)

Conventions.
* Matrices are indexed by `Fin n`, with integer entries each equal to 1 or -1;
  nonsingular means nonzero determinant (over ℤ, equivalently over ℚ).
* The extremal matrix `kraeuterMatrix n` has -1 at the diagonal positions `i < n - 1` and +1
  elsewhere (which diagonal position carries +1 does not matter: permuting rows and columns
  simultaneously changes neither the permanent nor nonsingularity).
* "Attained by" is stated as: `kraeuterMatrix n` is nonsingular, and every nonsingular
  (+1,-1)-matrix has permanent at most its permanent.
* The bound n ≥ 5 is needed: for n = 4 the maximum is 8 (example in the entry) while
  `kraeuterMatrix 4` has permanent 4. Checked by brute force: for n = 5 the maximum is 24,
  the permanent of `kraeuterMatrix 5` (determinant 16).
-/

namespace OMA.S_oeis_a087982

/-- The n × n (+1,-1)-matrix with -1 at the first n - 1 diagonal positions, +1 elsewhere. -/
def kraeuterMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => if i = j ∧ i.val < n - 1 then -1 else 1

/-- A (+1,-1)-matrix: every entry is 1 or -1. -/
def IsPlusMinusOne {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∀ i j, A i j = 1 ∨ A i j = -1

theorem main : ∀ n : ℕ, 5 ≤ n →
    (kraeuterMatrix n).det ≠ 0 ∧
    ∀ A : Matrix (Fin n) (Fin n) ℤ, IsPlusMinusOne A → A.det ≠ 0 →
      A.permanent ≤ (kraeuterMatrix n).permanent := by
  sorry

end OMA.S_oeis_a087982
