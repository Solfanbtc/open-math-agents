import Mathlib

/-!
# A080572: Number of ordered pairs (i,j), 0 <= i,j < n, for which (i & j) is nonzero, where & is the bitwise AND operator.

Source: https://oeis.org/A080572
Credit: @Solfanbtc

Conjecture (Richard Bean, OEIS A080572, comment): a(n) ≤ lcs(n), where lcs(n) = A063437(n)
is the cardinality of the largest critical set in any Latin square of order n.
Equivalently: for every n ≥ 1 there is a critical set of order n with at least a(n) entries.

Conventions:
* A Latin square of order `n` is `L : Fin n → Fin n → Fin n` with every row and every column
  injective. A set of given entries is a finset `C` of triples (row, column, symbol); `L`
  extends `C` if `L r c = s` for every `(r, c, s) ∈ C`.
* (A063437) `C` is a critical set if exactly one Latin square extends it and no proper subset
  of `C` has this property. lcs(n) is the largest size of a critical set; "a(n) ≤ lcs(n)" is
  stated as the existence of a critical set of size `≥ a(n)`, which is the same thing since
  critical sets of order `n` have at most `n^3` entries.
* A063437 has offset 1, so the conjecture is for `n ≥ 1`. Known values lcs(1..7) =
  0, 1, 3, 7, 11, 18, 25 against a(1..7) = 0, 1, 2, 7, 8, 15, 24, and the lower bounds of
  A063437 for n ≤ 17 (e.g. lcs(16) ≥ 181 > a(16) = 175) are consistent with it. For n = 2^k
  (Stinson and van Rees) and n = 2^k - 1 (Fu, Fu and Liao) the entry says critical sets of
  size a(n) are known.
* `a n` uses `Nat.land` (`&&&`); checked in Python and Lean (`#eval`) against %S, %T, %U.
-/

namespace OMA.S_oeis_a080572

/-- A080572: ordered pairs `(i, j)` with `i, j < n` and `i AND j ≠ 0`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range n ×ˢ Finset.range n).filter fun p => p.1 &&& p.2 ≠ 0).card

/-- A Latin square of order `n`. -/
def IsLatin {n : ℕ} (L : Fin n → Fin n → Fin n) : Prop :=
  (∀ r, Function.Injective (L r)) ∧ ∀ c, Function.Injective fun r => L r c

/-- `L` extends the given entries `C` (triples row, column, symbol). -/
def Extends {n : ℕ} (L : Fin n → Fin n → Fin n) (C : Finset (Fin n × Fin n × Fin n)) : Prop :=
  ∀ e ∈ C, L e.1 e.2.1 = e.2.2

/-- The entries `C` have a unique extension to a Latin square. -/
def UniquelyCompletable {n : ℕ} (C : Finset (Fin n × Fin n × Fin n)) : Prop :=
  ∃! L : Fin n → Fin n → Fin n, IsLatin L ∧ Extends L C

/-- A critical set: uniquely completable, and no proper subset is. -/
def IsCritical {n : ℕ} (C : Finset (Fin n × Fin n × Fin n)) : Prop :=
  UniquelyCompletable C ∧ ∀ C' ⊂ C, ¬ UniquelyCompletable C'

/-- Bean's conjecture: `a(n) ≤ lcs(n)`, i.e. some critical set of order `n` has at least
`a(n)` entries. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ C : Finset (Fin n × Fin n × Fin n), IsCritical C ∧ a n ≤ C.card := by
  sorry

end OMA.S_oeis_a080572
