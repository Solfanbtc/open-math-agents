import Mathlib

/-!
# A054639: Queneau numbers: numbers n such that the Queneau-Daniel permutation {1, 2, 3, ..., n} -> {n, 1, n-1, 2, n-2, 3, ...} is of order n

Source: https://oeis.org/A054639
Credit: @Solfanbtc

Conjecture (Charles R Greathouse IV, OEIS A054639, %F, Aug 02 2023): "I imagine
a(n) ≍ n log n, and numerics suggest that perhaps a(n) ~ k n log n for some constant k (which
seems to be around 1.122)." We state the stronger form, a(n) ~ k n log n for some constant
k > 0, which implies a(n) ≍ n log n. (The same comment says a(n) >> n log n holds, and
a(n) << n log^2 n on the Bateman-Horn-Stemmler conjecture; these are not conjectures of the
entry and are not stated. The numerical value of k is only approximate and is not stated.)

Conventions:
* The Queneau-Daniel permutation of {1, ..., n} sends position `i` to `n, 1, n-1, 2, ...`:
  `f(2j) = j` and `f(2j-1) = n+1-j`, i.e. `f i = i / 2` for even `i` and `n - (i-1)/2` for odd
  `i`. (Its inverse, the twist permutation, has the same order.) For n = 6 it is the sestina
  permutation 123456 -> 615243.
* "of order n", for n ≥ 1 (n = 0 would hold vacuously and is excluded): `f^[n]` is the identity on {1, ..., n} and `f^[t]` is not, for 1 ≤ t < n.
* a(n) (offset 1) is the n-th Queneau number, `Nat.nth IsQueneau (n - 1)`. The limit is taken
  along n → ∞ in ℝ; if the set were finite the ratio would tend to 0, so the statement
  includes that there are infinitely many Queneau numbers.
* Checked in Python: `IsQueneau` reproduces every term of %S, %T, %U; a(n) / (n log n) is about
  1.075, 1.093, 1.095 at n = 100, 1000, 2353.
-/

namespace OMA.S_oeis_a054639

open Filter Topology

/-- The Queneau-Daniel permutation of `{1, ..., n}`. -/
def qd (n i : ℕ) : ℕ := if i % 2 = 0 then i / 2 else n - (i - 1) / 2

/-- `n` is a Queneau number: the Queneau-Daniel permutation of `{1, ..., n}` has order `n`. -/
def IsQueneau (n : ℕ) : Prop :=
  1 ≤ n ∧ (∀ i ∈ Finset.Icc 1 n, (qd n)^[n] i = i) ∧
    ∀ t ∈ Finset.Ico 1 n, ¬ ∀ i ∈ Finset.Icc 1 n, (qd n)^[t] i = i

instance : DecidablePred IsQueneau := fun n => by unfold IsQueneau; infer_instance

/-- A054639: the `n`-th Queneau number (offset 1). -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsQueneau (n - 1)

/-- Greathouse's conjecture: `a(n) ~ k n log n` for some constant `k > 0`. -/
theorem main :
    ∃ k : ℝ, 0 < k ∧
      Tendsto (fun n : ℕ => (a n : ℝ) / ((n : ℝ) * Real.log n)) atTop (𝓝 k) := by
  sorry

end OMA.S_oeis_a054639
