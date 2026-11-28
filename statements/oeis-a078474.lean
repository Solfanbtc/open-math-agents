import Mathlib

/-!
# A078474: a(1)=a(2)=a(3)=1, a(n)=n-a(a(n-1))-a(a(n-2))-a(a(n-3)).

Source: https://oeis.org/A078474
Credit: @Solfanbtc

Conjecture (Sean A. Irvine, Jul 16 2022, OEIS A078474, verified for n <= 100000): A078474 is the
sequence of partial sums of A284680, i.e. a(n) = Σ_{k=1..n} b(k).

Definitions.
* A078474 by its recurrence (offset 1): a(1) = a(2) = a(3) = 1, a(n) = n - a(a(n-1)) - a(a(n-2))
  - a(a(n-3)) for n >= 4. The recurrence is not structurally well-founded, so `main` quantifies
  over every function satisfying it (the equation read in ℤ; `a 0` is unconstrained).
* A284680 (offset 1) is the fixed point of the morphism 0 ↦ 1, 1 ↦ 1000 starting with 1. The words
  w_0 = 1, w_{k+1} = σ(w_k) are successive prefixes of the fixed point (1, 1000, 1000111, ...), and
  w_n has length >= n (lengths 1, 4, 7, 19, 40, ...), so b(n) is the n-th letter of w_n.
Checked numerically: both sides agree for n <= 100000.
-/

namespace OMA.S_oeis_a078474

/-- The morphism 0 ↦ 1, 1 ↦ 1000 applied to a word. -/
def morph (w : List ℕ) : List ℕ := w.flatMap fun x => if x = 1 then [1, 0, 0, 0] else [1]

/-- b(n) = A284680(n), the n-th letter (n ≥ 1) of the fixed point. -/
def b (n : ℕ) : ℕ := (morph^[n] [1]).getD (n - 1) 0

/-- The recurrence of A078474. -/
def Spec (a : ℕ → ℕ) : Prop :=
  a 1 = 1 ∧ a 2 = 1 ∧ a 3 = 1 ∧
  ∀ n : ℕ, 4 ≤ n → (a n : ℤ) = n - a (a (n - 1)) - a (a (n - 2)) - a (a (n - 3))

theorem main : ∀ a : ℕ → ℕ, Spec a → ∀ n : ℕ, 1 ≤ n → a n = ∑ k ∈ Finset.Icc 1 n, b k := by
  sorry

end OMA.S_oeis_a078474
