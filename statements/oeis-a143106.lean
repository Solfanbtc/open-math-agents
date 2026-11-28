import Mathlib

/-!
# A143106: infinitely many odd degrees with a unique minimal positive polynomial equal to 1 on x+y=1

Source: https://oeis.org/A143106
Credit: @Solfanbtc

A143106: "Odd degrees for which (up to swapping of variables) there exists a unique polynomial
p(x,y), such that p(x,y)=1 when x+y=1, with positive coefficients and such that the number of
terms is minimal (equal to (d+3)/2)." Data 1, 3, 5, 9, 17, 21 (e.g. `x + y` for `d = 1` and
`x^3 + 3xy + y^3` for `d = 3`).

Conjecture (in the entry): this sequence is infinite ("nor if this sequence is infinite
(conjectured to be such)").

Definitions. For odd `d`, `Extremal d p` says: `p ∈ ℝ[x, y]` has total degree `d`, all its
nonzero coefficients are positive, it has exactly `(d + 3)/2` terms (the minimum, by the theorem
the entry refers to), and `p(x, y) = 1` whenever `x + y = 1`. `d` is a term iff such a `p`
exists and every such polynomial equals `p` or `p` with `x` and `y` swapped. `main` states that
the set of such odd `d` is infinite. (Not checked by computer: deciding membership needs the
classification of these polynomials, which the entry says is infeasible already at `d = 21`.)
-/

namespace OMA.S_oeis_a143106

open MvPolynomial

/-- `p` is an extremal polynomial of odd degree `d`. -/
def Extremal (d : ℕ) (p : MvPolynomial (Fin 2) ℝ) : Prop :=
  p.totalDegree = d ∧ (∀ m ∈ p.support, 0 < p.coeff m) ∧ p.support.card = (d + 3) / 2 ∧
    ∀ x y : ℝ, x + y = 1 → eval ![x, y] p = 1

/-- The polynomial with `x` and `y` swapped. -/
noncomputable def swapVars (p : MvPolynomial (Fin 2) ℝ) : MvPolynomial (Fin 2) ℝ :=
  rename (Equiv.swap 0 1) p

/-- `d` is a term of A143106: the extremal polynomial of degree `d` exists and is unique up to
swapping the variables. -/
def InSeq (d : ℕ) : Prop :=
  Odd d ∧ ∃ p, Extremal d p ∧ ∀ q, Extremal d q → q = p ∨ q = swapVars p

/-- The conjecture: A143106 is infinite. -/
theorem main : {d : ℕ | InSeq d}.Infinite := by
  sorry

end OMA.S_oeis_a143106
