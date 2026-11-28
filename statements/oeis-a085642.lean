import Mathlib

/-!
# A085642: Number of columns in the character table of the symmetric group S_n that have zero sum.

Source: https://oeis.org/A085642
Credit: @Solfanbtc

Conjecture (Vladeta Jovovic, OEIS A085642, comment, Jul 12 2003): a(n) equals the number of
partitions of n with at least one part congruent to 2 mod 4.
Status: per the entry, this conjecture was established by Christine Bessenrodt and Jørn B.
Olsson (Sep 13 2004). It is stated here as recorded in the entry.

Conventions:
* Columns of the character table of S_n are indexed by conjugacy classes, i.e. by cycle types,
  i.e. by partitions of n (`Equiv.Perm.partition`, which includes the fixed points as parts 1).
* Column sums: all irreducible characters of S_n are real-valued with Frobenius-Schur indicator
  +1 (they are realizable over ℚ), so for every g the column sum Σ_χ χ(g) equals the number of
  x ∈ S_n with x^2 = g (Frobenius-Schur). Hence the column of a class has zero sum iff no
  element of the class is a square. a(n) is therefore the number of partitions μ of n such that
  no permutation x of `Fin n` has x^2 of cycle type μ. (Mathlib has no enumeration of the
  irreducible characters of S_n, so the column sums are expressed through this identity.)
* Checked in Python for n ≤ 24: the number of cycle types that are not squares (some even part
  with odd multiplicity) reproduces %S (0, 1, 1, 2, 3, 6, 8, 12, ...) and equals the number of
  partitions with a part ≡ 2 (mod 4).
-/

namespace OMA.S_oeis_a085642

/-- A085642: the number of cycle types of `S_n` (columns of the character table) containing no
square, i.e. whose column has zero sum. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Nat.Partition (Fintype.card (Fin n)))).filter fun μ =>
    ¬ ∃ x : Equiv.Perm (Fin n), (x ^ 2).partition = μ).card

/-- Jovovic's conjecture (Bessenrodt-Olsson theorem). -/
theorem main :
    ∀ n : ℕ, a n =
      ((Finset.univ : Finset (Nat.Partition n)).filter fun μ => ∃ i ∈ μ.parts.toFinset, i % 4 = 2).card := by
  sorry

end OMA.S_oeis_a085642
