import Mathlib

/-!
# A065164: Permutation t->t+1 of Z, folded to N (Vatter: permutation classes of every growth rate)

Source: https://oeis.org/A065164
Credit: @Solfanbtc

The entry notes that the sequence (from a(2) = 4) is the "increasing oscillating sequence" of
V. Vatter, "Permutation classes of every growth rate above 2.48188" (arXiv:0807.2815), whose
abstract is quoted: "We prove that there are permutation classes (hereditary properties of
permutations) of every growth rate (Stanley-Wilf limit) at least lambda = approx 2.48187, the
unique real root of x^5-2x^4-2x^2-2x-1, thereby establishing a conjecture of Albert and Linton."

Status: PROVED (Vatter, Mathematika 57 (2011); the conjecture of Albert and Linton). We state
the theorem quoted in the entry.

Conventions.
* A permutation class is a set of permutations (of all lengths) closed under containment:
  `C n` is the set of its members of length n, and if σ ∈ C n contains π (of length k) then
  π ∈ C k. σ ∈ S_n contains π ∈ S_k if some order embedding f : Fin k ↪o Fin n satisfies
  σ(f i) < σ(f j) ↔ π i < π j for all i, j.
* "Growth rate (Stanley-Wilf limit) x" means |C n|^(1/n) → x (the limit exists and equals x).
* λ is the unique real root of x^5 - 2x^4 - 2x^2 - 2x - 1 (numerically 2.48187...; the other
  four roots are non-real), so it is stated for every real root λ.
-/

namespace OMA.S_oeis_a065164

/-- σ ∈ S_n contains the pattern π ∈ S_k. -/
def Contains {n k : ℕ} (σ : Equiv.Perm (Fin n)) (π : Equiv.Perm (Fin k)) : Prop :=
  ∃ f : Fin k ↪o Fin n, ∀ i j : Fin k, σ (f i) < σ (f j) ↔ π i < π j

/-- A permutation class: closed under pattern containment. -/
def IsPermClass (C : ∀ n : ℕ, Set (Equiv.Perm (Fin n))) : Prop :=
  ∀ (n k : ℕ) (σ : Equiv.Perm (Fin n)) (π : Equiv.Perm (Fin k)), σ ∈ C n → Contains σ π → π ∈ C k

theorem main : ∀ lam : ℝ, lam ^ 5 - 2 * lam ^ 4 - 2 * lam ^ 2 - 2 * lam - 1 = 0 →
    ∀ x : ℝ, lam ≤ x →
      ∃ C : ∀ n : ℕ, Set (Equiv.Perm (Fin n)), IsPermClass C ∧
        Filter.Tendsto (fun n : ℕ => (Nat.card (C n) : ℝ) ^ ((1 : ℝ) / n)) Filter.atTop
          (nhds x) := by
  sorry

end OMA.S_oeis_a065164
