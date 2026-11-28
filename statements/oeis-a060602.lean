import Mathlib

/-!
# A060602: Number of tilings of the d-dimensional zonotope constructed from d+3 vectors.

Source: https://oeis.org/A060602
Credit: @Solfanbtc

Conjectures from Colin Barker (Feb 20 2013), reported correct in the entry (Manfred Scheucher,
Feb 09 2022: see Proposition 7.1 in Ziegler, *Higher Bruhat orders and cyclic hyperplane
arrangements*, Topology 32, 1993):

  a(n) = 2*(-3 + 7*2^n + (-1 + 2^n)*n),
  G.f.: -2*(4*x^3 - 11*x^2 + 12*x - 4) / ((x-1)^2*(2*x-1)^2).

Both are stated below, as a conjunction (offset 0).

Conventions:
* The geometric definition (fine tilings of the zonotope `Z(d+3, d)`) is replaced by the
  combinatorial description given in the entry (Scheucher, after Felsner–Weil, *Sweeps,
  arrangements and signotopes*): a(n) is also the number of signotopes on `r+2` elements of
  rank `r`, here with `r = n + 1` (`d = n`, `D = d + 3 = r + 2` elements). This is the object
  Ziegler's Proposition 7.1 counts (the higher Bruhat order `B(r+2, r-1)`).
* A signotope on `m` elements of rank `r` is a map `X : ({1..m} choose r) → {+,-}` such that
  for every `r+1` indices `i_0 < i_1 < ... < i_r` forming `I`, the sequence
  `X(I - i_0), X(I - i_1), ..., X(I - i_r)` changes sign at most once. Here `X` is encoded by
  the set `S` of `r`-subsets of `Fin m` where it is `+`; the sign sequence is read along
  the elements of `I` in increasing order, `(List.finRange m).filter (· ∈ I)`.
* Checked in python by brute force: the counts for `n = 0..4` are 8, 24, 62, 148, 338, the
  first data terms; the g.f. expands to the closed form (checked for `n < 30`).
* The g.f. identity is stated in `ℚ⟦X⟧` as `A(x) * (x-1)^2 (2x-1)^2 = -2(4x^3-11x^2+12x-4)`
  (the denominator has constant term 1, so this is the same as the stated quotient).
-/

namespace OMA.S_oeis_a060602

open PowerSeries

/-- The number of sign changes in a sequence of signs. -/
def signChanges (l : List Bool) : ℕ := (l.zip l.tail).countP (fun p => p.1 != p.2)

/-- `S` (the set of `r`-subsets where the sign is `+`) defines a signotope of rank `r` on
`Fin m`: every `(r+1)`-set `I` has at most one sign change along `X(I - i_0), ..., X(I - i_r)`. -/
abbrev IsSignotope (m r : ℕ) (S : Finset (Finset (Fin m))) : Prop :=
  ∀ I ∈ (Finset.univ : Finset (Fin m)).powersetCard (r + 1),
    signChanges (((List.finRange m).filter (· ∈ I)).map (fun i => decide (I.erase i ∈ S))) ≤ 1

/-- The number of signotopes on `m` elements of rank `r`. -/
def numSignotopes (m r : ℕ) : ℕ :=
  (((Finset.univ : Finset (Fin m)).powersetCard r).powerset.filter (IsSignotope m r)).card

/-- A060602: the number of tilings of the `n`-dimensional zonotope from `n + 3` vectors,
i.e. the number of signotopes on `n + 3` elements of rank `n + 1`. -/
def a (n : ℕ) : ℕ := numSignotopes (n + 3) (n + 1)

/-- Barker's closed form and generating function for A060602. -/
theorem main :
    (∀ n : ℕ, (a n : ℤ) = 2 * (-3 + 7 * 2 ^ n + (-1 + 2 ^ n) * n)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (2 * X - 1) ^ 2) =
      -2 * (4 * X ^ 3 - 11 * X ^ 2 + 12 * X - 4) := by
  sorry

end OMA.S_oeis_a060602
