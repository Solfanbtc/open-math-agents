import Mathlib

/-!
# A091675: Positive integers n such that the trajectory of n under the Reverse and Add! operation carried out in base 4 (presumably) does not join the trajectory of any m < n.

Source: https://oeis.org/A091675
Credit: @Solfanbtc

The entry lists 49 terms (1, 3, 21, ..., 4117) and comments: "The conjecture that the base-4
trajectories of the terms do not join is based on the observation that if the trajectories of
two integers below 4120 join, this happens after at most 28 steps, while for any two terms
listed above the trajectories do not join within 1000 steps."

Formalization.
* `rev4 m` reverses the base-4 digits of `m`; one Reverse and Add! step is `T m = m + rev4 m`;
  the trajectory of `m` is `{T^[i] m | i : ℕ}`.
* Two trajectories *join* when they have a common element: `∃ i j, T^[i] m = T^[j] n`
  (forward orbits sharing one element coincide from there on).
* `n` is a term iff `n > 0` and the trajectory of `n` joins that of no `m` with `0 < m < n`.
* `main` states that the terms up to 4117 are exactly the 49 listed numbers, i.e. that the
  data of the entry is correct. Since joining is an equivalence relation on positive integers,
  this is equivalent to the conjecture of the comment (the trajectories of the 49 listed terms
  pairwise do not join) together with the finite, checked fact that every other `m ≤ 4117`
  joins the trajectory of a smaller number (python3: all 49 listed terms, and only they, come
  out when trajectories are followed for 300 steps).
-/

namespace OMA.S_oeis_a091675

/-- Reverse the base-4 digits. -/
def rev4 (m : ℕ) : ℕ := Nat.ofDigits 4 (Nat.digits 4 m).reverse

/-- One step of Reverse and Add! in base 4. -/
def T (m : ℕ) : ℕ := m + rev4 m

/-- The base-4 Reverse and Add! trajectories of `m` and `n` have a common element. -/
def Joins (m n : ℕ) : Prop := ∃ i j : ℕ, T^[i] m = T^[j] n

/-- `n` is a term of A091675. -/
def IsTerm (n : ℕ) : Prop := 0 < n ∧ ∀ m : ℕ, 0 < m → m < n → ¬ Joins m n

/-- The 49 terms listed in the entry. -/
def listed : List ℕ :=
  [1, 3, 21, 22, 26, 29, 31, 55, 256, 258, 262, 266, 269, 271, 282, 286, 287, 302, 312,
   413, 479, 511, 519, 551, 555, 719, 795, 799, 1026, 1029, 1034, 1037, 1066, 1549,
   1790, 2863, 3087, 3119, 4096, 4098, 4102, 4104, 4106, 4108, 4109, 4113, 4114, 4116, 4117]

theorem main : ∀ n : ℕ, n ≤ 4117 → (IsTerm n ↔ n ∈ listed) := by
  sorry

end OMA.S_oeis_a091675
