import Mathlib

/-!
# A058129: Number of nonisomorphic monoids (semigroups with identity) of order n.

Source: https://oeis.org/A058129
Credit: @Solfanbtc

The entry (formulas by Elijah Beregovsky, May 13 2025) states two conjectures:

* `a(n) = A027851(n-1) * (1 + o(1))`, where A027851(n) is the number of nonisomorphic semigroups
  of order `n` (Koubek and Rödl, *Note on the number of monoids of order n*, 1985);
* `a(n) = A058153(n) / n! * (1 + o(1))`, where A058153(n) is the number of labeled monoids of
  order `n` (Grillet, *Counting Semigroups*, 2014).

`f(n) = g(n) * (1 + o(1))` is stated as `f(n) / g(n) → 1` as `n → ∞` (for large `n` both
sides are positive). `main` is the conjunction of the two conjectures.

A structure of order `n` is encoded by its multiplication table on `Fin n`. Isomorphism of
tables is relabeling by a permutation of `Fin n`, which is isomorphism of magmas (for monoids a
multiplicative bijection automatically preserves the identity). Every semigroup (monoid) of
order `n` is isomorphic to one carried by `Fin n`, so `numSemigroups n` and `numMonoids n` are
A027851(n) and A058129(n). These definitions were evaluated with `#eval`: `numMonoids` gives
`0, 1, 2, 7` for `n = 0..3` (A058129), `numSemigroups` gives `1, 1, 5, 24` (A027851) and
`numLabeledMonoids` gives `1, 4, 33` for `n = 1..3` (A058153).
-/

namespace OMA.S_oeis_a058129

/-- The table `m` is associative. -/
def IsSemigroupTable {n : ℕ} (m : Fin n → Fin n → Fin n) : Prop :=
  ∀ a b c, m (m a b) c = m a (m b c)

/-- The table `m` is associative and has a two-sided identity. -/
def IsMonoidTable {n : ℕ} (m : Fin n → Fin n → Fin n) : Prop :=
  IsSemigroupTable m ∧ ∃ e, ∀ a, m e a = a ∧ m a e = a

/-- Two tables are isomorphic: some permutation `σ` of `Fin n` carries `m` to `m'`. -/
def TableIso {n : ℕ} (m m' : Fin n → Fin n → Fin n) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), ∀ a b, σ (m a b) = m' (σ a) (σ b)

instance {n : ℕ} (m : Fin n → Fin n → Fin n) : Decidable (IsSemigroupTable m) := by
  unfold IsSemigroupTable; infer_instance

instance {n : ℕ} (m : Fin n → Fin n → Fin n) : Decidable (IsMonoidTable m) := by
  unfold IsMonoidTable; infer_instance

instance {n : ℕ} (m m' : Fin n → Fin n → Fin n) : Decidable (TableIso m m') := by
  unfold TableIso; infer_instance

/-- Number of isomorphism classes of tables on `Fin n` satisfying `P` (each table is sent to the
set of tables satisfying `P` isomorphic to it; distinct classes give distinct sets). -/
def numClasses {n : ℕ} (P : (Fin n → Fin n → Fin n) → Prop) [DecidablePred P] : ℕ :=
  ((Finset.univ.filter P).image fun m => (Finset.univ.filter P).filter (TableIso m)).card

/-- A058153: number of labeled monoids of order `n`. -/
def numLabeledMonoids (n : ℕ) : ℕ := (Finset.univ.filter (@IsMonoidTable n)).card

/-- A058129: number of nonisomorphic monoids of order `n`. -/
def numMonoids (n : ℕ) : ℕ := numClasses (@IsMonoidTable n)

/-- A027851: number of nonisomorphic semigroups of order `n`. -/
def numSemigroups (n : ℕ) : ℕ := numClasses (@IsSemigroupTable n)

/-- Both conjectures of A058129: `a(n) ~ A027851(n-1)` and `a(n) ~ A058153(n) / n!`. -/
theorem main :
    Filter.Tendsto (fun n : ℕ => (numMonoids n : ℝ) / (numSemigroups (n - 1) : ℝ))
      Filter.atTop (nhds 1) ∧
    Filter.Tendsto
      (fun n : ℕ => (numMonoids n : ℝ) / ((numLabeledMonoids n : ℝ) / (n.factorial : ℝ)))
      Filter.atTop (nhds 1) := by
  sorry

end OMA.S_oeis_a058129
