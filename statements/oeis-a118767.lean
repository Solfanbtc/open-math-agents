import Mathlib

/-!
# A118767: a fixed point of the Levenshtein-greedy permutation A118763 beyond 10^8

Source: https://oeis.org/A118767 (with https://oeis.org/A118763)
A118763 (offset 0): `g(0) = 0`, and `g(n+1)` is the smallest number not occurring earlier whose
decimal representation has Levenshtein distance 1 to that of `g(n)`:
0, 1, 2, ..., 9, 19, 10, 11, ..., 18, 28, 20, ... (a permutation of the natural numbers).
A118767 lists its fixed points (which are also the fixed points of A118764 = `g⁻¹`,
A118765 = `g ∘ g` and A118766): 0, 1, ..., 9, 29, 49, 69, 89, 200004, 400004, ...
Comment (Joshua Zucker, May 14 2006): "No more terms less than 10^4. Looking at the pattern
mod 9, I conjecture that there will be more terms past 10^8."

We state the conjecture literally: `g` has a fixed point `m > 10^8`.
(The terms 200004, ..., 1460005 found since, by Michael S. Branicky in 2026, lie between `10^4`
and `10^8`; whether the 2026 b-file already reaches past `10^8` was not checked here.)

Formalization. Decimal representations are digit lists, most significant first (`0` is `[0]`).
Levenshtein distance 1 between two lists means exactly one substitution, insertion or deletion:
same length and exactly one differing position, or one list is the other with one digit inserted.
Checked: an `#eval` with this definition (and a bounded search) reproduces the 73 listed terms of
A118763 and gives the fixed points 0, ..., 9, 29, 49, 69 below 73.

Credit: @Solfanbtc
-/

namespace OMA.S_oeis_a118767

/-- The decimal representation of `n`, most significant digit first. -/
def dec (n : ℕ) : List ℕ := if n = 0 then [0] else (Nat.digits 10 n).reverse

/-- `s` and `t` are at Levenshtein distance exactly 1. -/
def OneEdit (s t : List ℕ) : Prop :=
  (s.length = t.length ∧ ((List.range s.length).filter (fun i => s[i]? ≠ t[i]?)).length = 1) ∨
  (∃ i ≤ s.length, ∃ x : ℕ, t = s.insertIdx i x) ∨
  (∃ i ≤ t.length, ∃ x : ℕ, s = t.insertIdx i x)

/-- `gList n = [g(0), ..., g(n)]` for A118763. -/
noncomputable def gList : ℕ → List ℕ
  | 0 => [0]
  | n + 1 =>
    let l := gList n
    l ++ [sInf {k : ℕ | k ∉ l ∧ OneEdit (dec (l.getLastD 0)) (dec k)}]

/-- A118763. -/
noncomputable def g (n : ℕ) : ℕ := (gList n).getD n 0

theorem main : ∃ m : ℕ, 10 ^ 8 < m ∧ g m = m := by
  sorry

end OMA.S_oeis_a118767
