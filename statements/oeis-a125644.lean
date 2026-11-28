import Mathlib

/-!
# A125644: Table with T(n,k) = the number of Dyck paths whose ascent lengths, in order, are the k-th composition of n, for the standard composition order.

Source: https://oeis.org/A125644
Credit: @Solfanbtc

Claim (entry formula, Mikhail Kurkov, noticed by the Sequence Machine):
a(n) = A347205(A035327(n)) for n ≥ 0, where a is the flattened table.

Conventions.
* Flattening and standard order (A066099): row 0 is the empty composition of 0; for n ≥ 1, row n
  holds the 2^(n-1) compositions of n, and the entry with flat index N ≥ 1 is the standard
  composition of N: write N in binary (most significant bit first), cut it into blocks that each
  begin with a 1, and take the block lengths (11 = 1011₂ ↦ 10|1|1 ↦ (2,1,1), as in the entry's
  example a(11) = 3). For N = 0 this gives the empty composition.
* A Dyck path of semilength m is a word in U (`true`) and D (`false`) of length 2m whose
  prefixes never have more D than U and which ends at height 0; its ascent lengths are the
  lengths of its maximal runs of U, in order. a(N) counts the Dyck paths of semilength
  (sum of the composition) whose ascent lengths are the composition of N.
* A347205: b(0) = 1, b(2n+1) = b(n), b(2n) = b(n) + b(n - 2^v₂(n)) for n > 0.
* A035327: A035327(0) = 1 and A035327(n) = 2^(⌊log₂ n⌋+1) - 1 - n for n ≥ 1 (complement the
  binary digits).
Python checks: these definitions give all 98 listed terms; the conjecture holds for N < 2^16.
-/

namespace OMA.S_oeis_a125644

/-- Height after the first `i` steps (`true` = up). -/
def height (w : List Bool) (i : ℕ) : ℤ := ((w.take i).map fun s => if s then (1 : ℤ) else -1).sum

/-- `w` is a Dyck path. -/
def IsDyck (w : List Bool) : Prop :=
  (∀ i ∈ Finset.range (w.length + 1), 0 ≤ height w i) ∧ height w w.length = 0

instance : DecidablePred IsDyck := fun w => by unfold IsDyck; infer_instance

/-- Lengths of the maximal runs of `true` (ascents), in order. -/
def ascents (w : List Bool) : List ℕ := ((w.splitOn false).filter (· ≠ [])).map List.length

/-- The standard composition (A066099) with index `N`; empty for `N = 0`. -/
def comp (N : ℕ) : List ℕ := ((Nat.digits 2 N).reverse.splitOn 1).tail.map (·.length + 1)

/-- A125644(N): Dyck paths whose ascent lengths are the standard composition `comp N`. -/
def a (N : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin (2 * (comp N).sum) → Bool)).filter
    (fun f => IsDyck (List.ofFn f) ∧ ascents (List.ofFn f) = comp N)).card

/-- A347205. -/
def A347205 : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
    if (n + 1) % 2 = 1 then A347205 ((n + 1) / 2)
    else A347205 ((n + 1) / 2) + A347205 ((n + 1) / 2 - 2 ^ padicValNat 2 ((n + 1) / 2))
decreasing_by
  · omega
  · omega
  · exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (by omega)

/-- A035327: binary complement of `n`, with A035327(0) = 1. -/
def A035327 (n : ℕ) : ℕ := if n = 0 then 1 else 2 ^ (Nat.log 2 n + 1) - 1 - n

theorem main : ∀ n : ℕ, a n = A347205 (A035327 n) := by
  sorry

end OMA.S_oeis_a125644
