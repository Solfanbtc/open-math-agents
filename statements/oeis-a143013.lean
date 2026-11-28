import Mathlib

/-!
# A143013: Number of Motzkin n-paths with two kinds of level steps one of which is a final step.

Source: https://oeis.org/A143013 (Michael Somos, 2008; conjecture by R. J. Mathar,
Oct 25 2012; OEIS Foundation, CC BY-SA 4.0).
Credit: @Solfanbtc

Definition (OEIS formula line): a(n) is the number of words of length n on the alphabet
{U, D, L, F}, where U is an up step, D a down step, L and F are level steps, which are Motzkin
paths (they never go below the starting level and end at it), and in which F can only be
immediately followed by D or by the end of the word. Example: a(3) = 7 (LLL, LLF, LUD, UDL,
UDF, ULD, UFD).

Conjecture (OEIS): (n+2)*a(n) - (2*n+1)*a(n-1) + 3*(1-n)*a(n-2) + 2*(5-2*n)*a(n-3) = 0.

Formalization notes.
* A word of length n is a function `Fin n → Step`; the height after the first i steps is
  the number of U's minus the number of D's among them.
* The recurrence involves a(n-3), so it is stated for n ≥ 3 (offset 0), over ℤ.
* Python checks: a brute force over all words of length ≤ 9 and the g.f. equation
  A = 1 + x + xA + (xA)^2 both reproduce the listed terms; the recurrence holds for
  3 ≤ n < 400 (the latter computed from the g.f.).
-/

namespace OMA.S_oeis_a143013

/-- The four steps, encoded as `Fin 4`: 0 = U, 1 = D, 2 = L, 3 = F. -/
abbrev Step := Fin 4

namespace Step
/-- Up step. -/
def U : Step := 0
/-- Down step. -/
def D : Step := 1
/-- Level step of the first kind. -/
def L : Step := 2
/-- Level step of the second kind (only before D or at the end). -/
def F : Step := 3

/-- Height change of a step. -/
def delta (s : Step) : ℤ := if s = U then 1 else if s = D then -1 else 0
end Step

/-- Height after the first `i` steps of `w`. -/
def height {n : ℕ} (w : Fin n → Step) (i : ℕ) : ℤ :=
  ∑ j : Fin n, if j.val < i then (w j).delta else 0

/-- `w` is a Motzkin path (never below 0, ends at 0) in which every F is immediately followed by
D or by the end of the word. -/
def IsGood {n : ℕ} (w : Fin n → Step) : Prop :=
  (∀ i ≤ n, 0 ≤ height w i) ∧ height w n = 0 ∧
  ∀ i j : Fin n, j.val = i.val + 1 → w i = Step.F → w j = Step.D

instance {n : ℕ} (w : Fin n → Step) : Decidable (IsGood w) := by
  unfold IsGood; infer_instance

/-- A143013(n). -/
def a (n : ℕ) : ℕ := (Finset.univ.filter (fun w : Fin n → Step => IsGood w)).card

theorem main : ∀ n : ℕ, 3 ≤ n →
    ((n : ℤ) + 2) * a n - (2 * (n : ℤ) + 1) * a (n - 1) + 3 * (1 - (n : ℤ)) * a (n - 2)
      + 2 * (5 - 2 * (n : ℤ)) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a143013
