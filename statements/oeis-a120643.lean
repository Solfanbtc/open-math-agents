import Mathlib

/-!
# A120643: Table T(n,k) = number of fractal initial sequences (where new values are successive integers) of length n whose last term is k.

Source: https://oeis.org/A120643
Credit: @Solfanbtc

Conjecture (entry comment): column 1 of this array is A007059.

Definitions (entry comment).
* A finite sequence s(1..n) of positive integers is a fractal initial sequence when (a) the
  first instances of its values occur in order 1, 2, 3, ... ("1,1,2,3 is OK, but 1,1,3,2 is
  not"), and (b) removing the first instance of each value leaves an initial subsegment (a
  prefix) of s. T(n,k) counts those of length n with last term k (1 ≤ k ≤ n). Values are at
  most n, so we count words in {1..n}^n. python3 reproduces the 78 data terms (and the total
  2^(n-1) per row); `#eval` for n ≤ 5.
* A007059 ("number of balanced ordered trees with n nodes"): we use the characterization given
  in A007059 by Joerg Arndt, for n ≥ 1 the number of compositions of n in which all parts after
  the first are smaller than the first part (data 1, 1, 2, 3, 5, 8, 14, ... for n = 1, 2, ...).
* With the offsets of both entries, column 1 of the table matches A007059(n) for n ≥ 1:
  1, 1, 2, 3, 5, 8, 14, 24, 43, 77, 140, 256 (python3, n ≤ 12).
* Statement: T(n, 1) = A007059(n) for every n ≥ 1.
-/

namespace OMA.S_oeis_a120643

/-- Remove the first instance of each value. -/
def removeFirsts (s : List ℕ) : List ℕ :=
  (List.range s.length).filterMap fun i =>
    if s.getD i 0 ∈ s.take i then some (s.getD i 0) else none

/-- New values appear in the order 1, 2, 3, .... -/
def NewInOrder (s : List ℕ) : Prop :=
  ∀ i ∈ Finset.range s.length,
    s.getD i 0 ∈ s.take i ∨ s.getD i 0 = (s.take i).toFinset.card + 1

/-- `s` is a fractal initial sequence. -/
def IsFIS (s : List ℕ) : Prop := NewInOrder s ∧ removeFirsts s <+: s

instance : DecidablePred IsFIS := fun s => by unfold IsFIS NewInOrder; infer_instance

/-- T(n, k): fractal initial sequences of length `n` (values in 1..n) ending in `k`. -/
def T (n k : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n → Fin n)).filter fun f =>
    let s := List.ofFn fun i => (f i : ℕ) + 1
    IsFIS s ∧ s.getLastD 0 = k).card

/-- A007059(n), n ≥ 1: compositions of `n` whose later parts are all smaller than the first. -/
def A007059 (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Composition n)).filter fun c =>
    ∀ x ∈ c.blocks.tail, x < c.blocks.headD 0).card

theorem main : ∀ n : ℕ, 1 ≤ n → T n 1 = A007059 n := by
  sorry

end OMA.S_oeis_a120643
