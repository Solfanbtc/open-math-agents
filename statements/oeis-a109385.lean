import Mathlib

/-!
# A109385: Maximum number of prime implicants of a symmetric function of n Boolean variables.

Source: https://oeis.org/A109385
Credit: @Solfanbtc

A *term* (conjunction of literals) on `n` variables is `t : Fin n → Option Bool`: `t i = some b`
fixes `x_i = b`, `t i = none` leaves `x_i` free. It is an *implicant* of
`f : (Fin n → Bool) → Bool` if `f x = true` for every `x` satisfying `t`, and a *prime implicant*
if moreover deleting any one of its literals gives a non-implicant (equivalently, no proper
subterm is an implicant, since a subterm of a subterm of `t` is satisfied by more points).
`f` is *symmetric* if it is invariant under every permutation of the variables.

A109385(n) is the largest number of prime implicants of a symmetric `f` of `n` variables, and
A003039(n) the largest number of prime implicants of an arbitrary `f`; trivially
A109385 ≤ A003039. Conjecture (in the entry: "many people have conjectured that this sequence is
equal to A003039"; see Knuth, TAOCP 4A, 7.1.1): A109385(n) = A003039(n) for all `n`, i.e. the
maximum is always attained by a symmetric function. `main` states it as: every `f` has at most as
many prime implicants as some symmetric `g`.

python3 brute force over all Boolean functions: both maxima are 1, 2, 6, 13 for `n = 1, ..., 4`,
matching the data of both entries.
-/

namespace OMA.S_oeis_a109385

/-- `x` satisfies the term `t`. -/
def Sat {n : ℕ} (t : Fin n → Option Bool) (x : Fin n → Bool) : Prop :=
  ∀ i, t i = none ∨ t i = some (x i)

/-- `t` is an implicant of `f`. -/
def IsImplicant {n : ℕ} (f : (Fin n → Bool) → Bool) (t : Fin n → Option Bool) : Prop :=
  ∀ x, Sat t x → f x = true

/-- `t` is a prime implicant of `f`. -/
def IsPrimeImplicant {n : ℕ} (f : (Fin n → Bool) → Bool) (t : Fin n → Option Bool) : Prop :=
  IsImplicant f t ∧ ∀ i, t i ≠ none → ¬ IsImplicant f (Function.update t i none)

/-- The number of prime implicants of `f`. -/
noncomputable def numPrimeImplicants {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ := by
  classical exact (Finset.univ.filter (IsPrimeImplicant f)).card

/-- `f` is a symmetric Boolean function. -/
def IsSymmetric {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (x : Fin n → Bool), f (x ∘ σ) = f x

/-- Conjecture: A109385 = A003039, i.e. symmetric functions attain the maximum number of prime
implicants. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∀ f : (Fin n → Bool) → Bool,
    ∃ g : (Fin n → Bool) → Bool, IsSymmetric g ∧ numPrimeImplicants f ≤ numPrimeImplicants g := by
  sorry

end OMA.S_oeis_a109385
