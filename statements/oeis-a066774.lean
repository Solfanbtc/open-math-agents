import Mathlib

/-!
# A066774: A066728(a(n))=3.

Source: https://oeis.org/A066774
Credit: @Solfanbtc

A066728(n) is the number of `k ∈ {1, …, n-1}` such that `(n + k + n k)/(n - k)` is an integer.
A066774 lists the `n` with A066728(n) = 3, in increasing order: 4, 13, 15, 19, 21, 27, ….

Conjecture (Benoit Cloitre, 2002): the set of `k` such that `a(k+1) - a(k) = 2` is infinite,
i.e. infinitely often two consecutive terms of A066774 differ by 2. With `a(k) = Nat.nth IsTerm
(k - 1)` (offset 1), the index shift does not affect infiniteness, so `main` uses `Nat.nth`
directly. Checked with python3: the definition reproduces the data of A066728 and A066774; the
gaps equal to 2 start at 13, 19, 35, 37, 51, ….
-/

namespace OMA.S_oeis_a066774

/-- A066728(n). -/
def c (n : ℕ) : ℕ :=
  ((Finset.Icc 1 (n - 1)).filter (fun k => (n - k) ∣ (n + k + n * k))).card

/-- `n` is a term of A066774. -/
def IsTerm (n : ℕ) : Prop := c n = 3

/-- Cloitre's conjecture: infinitely many consecutive terms of A066774 differ by 2. -/
theorem main : {k : ℕ | Nat.nth IsTerm (k + 1) = Nat.nth IsTerm k + 2}.Infinite := by
  sorry

end OMA.S_oeis_a066774
