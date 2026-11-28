import Mathlib

/-!
# A100036: first occurrences in A100035

Source: https://oeis.org/A100036 (with https://oeis.org/A100035 and https://oeis.org/A096376)
A100035 (offset 1): `a(1) = 1`, and "a(n+1) occurs not earlier as a neighbor of terms = a(n):
either it is the greatest number < a(n) or, if no such number exists, the smallest number > a(n)".
That is, `a(n+1)` is the greatest positive `y < a(n)` such that `a(n)` and `y` have not yet been
adjacent in `a(1), ..., a(n)`, and if there is no such `y`, the smallest `y > a(n)` with that
property: 1, 2, 3, 1, 4, 3, 5, 4, 2, 5, 1, 6, ...
A100036(n) (offset 1) is the smallest `m` with `A100035(m) = n`: 1, 2, 3, 5, 7, 12, 14, 23, ...

Conjecture (Ralf Stephan, May 15 2007): "a(n) = partial sums of sequence
[1,1,1,2,2,5,2,9,2,13,2,17,...]. In other words, a(n) consists of the numbers 1,2,3 and the
sequences A096376 and A096376+2 interspersed." With `A096376(k) = k + (k-1)^2 + (k+1)^2`
(5, 12, 23, 38, ... for `k = 1, 2, 3, 4, ...`), this reads: `a(1), a(2), a(3) = 1, 2, 3` and, for
every `k ≥ 1`, `a(2k+2) = A096376(k)` and `a(2k+3) = A096376(k) + 2`. (We use the second phrasing;
the first one is garbled in the entry at "n/2-7", and both agree with all listed terms.)

Formalization notes. `terms n` is the list `[A100035(1), ..., A100035(n+1)]`. When no admissible
`y < x` exists, the smallest admissible `y > x` is searched among `x+1, ..., x+L+1`, where `L` is
the current length: at most `L - 1` pairs are adjacent so far, so one of these `L + 1` numbers is
admissible and the bounded search returns the true smallest one.
Checked with python3 (an independent implementation): it reproduces the 88 listed terms of
A100035 and the 54 listed terms of A100036, and the conjecture holds for all `n < 633`.

Credit: @Solfanbtc
-/

namespace OMA.S_oeis_a100036

/-- `x` and `y` are adjacent somewhere in the list `l`. -/
def adjacent (l : List ℕ) (x y : ℕ) : Bool :=
  (l.zip l.tail).any (fun p => (p.1 == x && p.2 == y) || (p.1 == y && p.2 == x))

/-- The next term of A100035 after the list `l` of the terms so far. -/
def next (l : List ℕ) : ℕ :=
  let x := l.getLast?.getD 1
  match ((List.range (x - 1)).map (· + 1)).reverse.find? (fun y => !adjacent l x y) with
  | some y => y
  | none => (((List.range (l.length + 1)).map (fun i => x + 1 + i)).find?
      (fun y => !adjacent l x y)).getD 0

/-- `terms n = [A100035(1), ..., A100035(n+1)]`. -/
def terms : ℕ → List ℕ
  | 0 => [1]
  | n + 1 => terms n ++ [next (terms n)]

/-- A100035 (offset 1). -/
def A100035 (m : ℕ) : ℕ := (terms m).getD (m - 1) 0

/-- A100036: the smallest `m ≥ 1` with `A100035(m) = n`. -/
noncomputable def a (n : ℕ) : ℕ := sInf {m : ℕ | 1 ≤ m ∧ A100035 m = n}

/-- A096376: `k + (k-1)^2 + (k+1)^2`. -/
def A096376 (k : ℕ) : ℕ := k + (k - 1) ^ 2 + (k + 1) ^ 2

theorem main :
    a 1 = 1 ∧ a 2 = 2 ∧ a 3 = 3 ∧
    ∀ k : ℕ, 1 ≤ k → a (2 * k + 2) = A096376 k ∧ a (2 * k + 3) = A096376 k + 2 := by
  sorry

end OMA.S_oeis_a100036
