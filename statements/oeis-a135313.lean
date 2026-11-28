import Mathlib

/-!
# A135313: transitive reflexive early confluent relations by maximal out-degree.

Source: https://oeis.org/A135313 (Alois P. Heinz, 2007; conjecture by Vaclav Kotesovec,
Nov 20 2021; OEIS Foundation, CC BY-SA 4.0).
Credit: @Solfanbtc

Definition (OEIS): T(n,k) (n ≥ k ≥ 0) is the number of transitive reflexive early confluent
binary relations R on n labeled elements with k = max_x |{y : x R y}|. R is early confluent iff
(x R y and x R z) implies (y R z or z R y), for all x, y, z.

Conjecture (OEIS): for fixed k ≥ 0,
  A135313(n+k, n) ~ n! * n^(2k) / (2^(k+1) * k! * log(2)^(n+k+1))   as n → ∞.

Formalization notes.
* The n labeled elements are `Fin n`; a binary relation is a function `Fin n → Fin n → Bool`.
* The maximum over the empty set of elements (n = 0) is taken to be 0, which gives
  T(0,0) = 1 as in the OEIS data. For n ≥ k we count relations whose maximal out-degree is k
  (out-degrees count x itself, since R is reflexive).
* "~" is asymptotic equivalence of real sequences as n → ∞ (`Asymptotics.IsEquivalent`), and
  `Real.log 2` is the natural logarithm, as in the OEIS.
* Python checks: a brute force over all relations on at most 4 elements and the e.g.f. formula
  of the entry both reproduce the listed rows; for k = 0..3 the ratio of T(n+k,n) to the
  conjectured expression at n = 60 is about 1.000, 1.014, 1.12 and 1.34, decreasing towards 1.
  (The case k = 0 is the known asymptotic of the Fubini numbers A000670.)
-/

namespace OMA.S_oeis_a135313

open Asymptotics Filter

/-- Transitive, reflexive and early confluent. -/
def IsGood {n : ℕ} (R : Fin n → Fin n → Bool) : Prop :=
  (∀ x, R x x = true) ∧
  (∀ x y z, R x y = true → R y z = true → R x z = true) ∧
  (∀ x y z, R x y = true → R x z = true → R y z = true ∨ R z y = true)

instance {n : ℕ} (R : Fin n → Fin n → Bool) : Decidable (IsGood R) := by
  unfold IsGood; infer_instance

/-- max_x |{y : x R y}| (0 when there is no element). -/
def maxOutDegree {n : ℕ} (R : Fin n → Fin n → Bool) : ℕ :=
  Finset.univ.sup (fun x => (Finset.univ.filter (fun y => R x y = true)).card)

/-- T(n,k) = A135313(n,k). -/
def T (n k : ℕ) : ℕ :=
  (Finset.univ.filter (fun R : Fin n → Fin n → Bool => IsGood R ∧ maxOutDegree R = k)).card

theorem main : ∀ k : ℕ,
    (fun n : ℕ => (T (n + k) n : ℝ)) ~[atTop]
      (fun n : ℕ => (n.factorial : ℝ) * (n : ℝ) ^ (2 * k) /
        (2 ^ (k + 1) * (k.factorial : ℝ) * Real.log 2 ^ (n + k + 1))) := by
  sorry

end OMA.S_oeis_a135313
