import Mathlib

/-!
# A100759: Beginning with 2, least prime not occurring earlier such that the concatenation of first n terms has the least prime factor prime(n).

Source: https://oeis.org/A100759
Credit: @Solfanbtc

`a(1) = 2`, and for `n ≥ 2`, `a(n)` is the least prime not among `a(1), ..., a(n-1)` such that
the least prime factor of the decimal concatenation `a(1) a(2) ⋯ a(n)` is `prime(n)`.
Data: 2, 7, 5, 17, 127, 3, 347, ...; e.g. `a(2) = 7`, as the least prime factor of 27 is 3.
python3 reproduces the first 39 terms.

Conjecture (in the entry): every prime is a member. The conjecture presupposes that the sequence
is infinite, i.e. that a candidate exists at every step, so `main` states both: the candidate set
of every step is nonempty, and every prime occurs.

`terms k` is the list `[a(1), ..., a(k+1)]`; its step `k + 1` picks `a(k+2)` with least prime
factor `prime(k+2) = Nat.nth Nat.Prime (k+1)` (via `sInf`, which is the least candidate when one
exists).
-/

namespace OMA.S_oeis_a100759

/-- The decimal concatenation of a list of numbers. -/
def cat (l : List ℕ) : ℕ :=
  l.foldl (fun acc p => acc * 10 ^ (Nat.digits 10 p).length + p) 0

/-- The candidates for the term after the list `l` (which has `k + 1` terms). -/
def candidates (l : List ℕ) (k : ℕ) : Set ℕ :=
  {p | p.Prime ∧ p ∉ l ∧ (cat (l ++ [p])).minFac = Nat.nth Nat.Prime (k + 1)}

/-- `terms k = [a(1), ..., a(k+1)]`. -/
noncomputable def terms : ℕ → List ℕ
  | 0 => [2]
  | k + 1 => let l := terms k; l ++ [sInf (candidates l k)]

/-- The sequence never gets stuck, and every prime is one of its terms. -/
theorem main :
    (∀ k : ℕ, (candidates (terms k) k).Nonempty) ∧
    (∀ p : ℕ, p.Prime → ∃ k : ℕ, p ∈ terms k) := by
  sorry

end OMA.S_oeis_a100759
