import Mathlib

/-!
# A033321: Binomial transform of Fine's sequence A000957: 1, 0, 1, 2, 6, 18, 57, 186, ...

Source: https://oeis.org/A033321
Credit: @Solfanbtc

Conjecture (Colin Defant, Aug 30 2020; Defant and Zheng, "Stack-Sorting with
Consecutive-Pattern-Avoiding Stacks", arXiv:2008.12297): `a(n)` is the number of
permutations of length `n` that are sorted to the identity by a consecutive-231-avoiding
stack followed by a classical-21-avoiding stack.

Conventions (pattern-avoiding stacks in the sense of Cerbai, Claesson and Ferrari, as used by
Defant and Zheng):
* A `σ`-avoiding stack reads its input from left to right. At each step, if pushing the next
  input entry would make the stack contents, read from top to bottom, contain `σ`, the top
  entry is popped to the output; otherwise the next entry is pushed. When the input is
  exhausted the remaining entries are popped. For "consecutive" `σ` an occurrence must use
  adjacent stack positions; for "classical" `σ` any positions.
* The classical-21-avoiding stack is West's stack-sorting map `s`. The permutations counted
  are those `π` with `s (s_231 π) = id`, the 231-stack acting first.
* Permutations of length `n` are the lists that are permutations of `[1, 2, ..., n]`.

With these conventions the count was checked by brute force in Python for `n ≤ 8`
(1, 1, 2, 6, 21, 79, 311, 1265, 5275); reading the stack from bottom to top instead gives the
Catalan numbers, so the reading direction matters.

The sequence itself is defined as its name says. `fineShift m = A000957(m + 1)` is Fine's
sequence `1, 0, 1, 2, 6, 18, 57, 186, ...`, determined by `A000957(1) = 1` and the formula
`Catalan(n) = 2 * A000957(n + 1) + A000957(n)` for `n ≥ 1` (from A000957), and
`a n = Σ_{k=0..n} binomial(n, k) * fineShift (n - k)`.
-/

namespace OMA.S_oeis_a033321

/-- `A000957(m + 1)`: Fine's sequence starting `1, 0, 1, 2, 6, 18, ...`. -/
def fineShift : ℕ → ℕ
  | 0 => 1
  | m + 1 => (catalan (m + 1) - fineShift m) / 2

/-- A033321: the binomial transform of `1, 0, 1, 2, 6, 18, 57, ...`. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), n.choose k * fineShift (n - k)

/-- `w` contains the consecutive pattern 231: adjacent entries `x, y, z` with `z < x < y`. -/
def hasConsec231 : List ℕ → Bool
  | x :: y :: z :: rest => (decide (z < x) && decide (x < y)) || hasConsec231 (y :: z :: rest)
  | _ => false

/-- `w` contains the classical pattern 21: some entry is followed (not necessarily
adjacently) by a smaller one. -/
def hasClassical21 (w : List ℕ) : Bool := !decide (w.Pairwise (· ≤ ·))

/-- One pass through a stack that refuses any push after which `forbidden` holds of the stack
contents read from top to bottom. Arguments: remaining input, stack (head = top), output so far
(reversed). -/
def stackPass (forbidden : List ℕ → Bool) : List ℕ → List ℕ → List ℕ → List ℕ
  | [], st, out => out.reverse ++ st
  | x :: xs, [], out => stackPass forbidden xs [x] out
  | x :: xs, t :: ts, out =>
      if forbidden (x :: t :: ts) then stackPass forbidden (x :: xs) ts (t :: out)
      else stackPass forbidden xs (x :: t :: ts) out
termination_by inp st => 2 * inp.length + st.length

/-- The consecutive-231-avoiding stack `s_231`. -/
def s231 (π : List ℕ) : List ℕ := stackPass hasConsec231 π [] []

/-- The classical-21-avoiding stack, i.e. West's stack-sorting map `s`. -/
def west (π : List ℕ) : List ℕ := stackPass hasClassical21 π [] []

/-- The identity permutation `[1, 2, ..., n]`. -/
def idList (n : ℕ) : List ℕ := (List.range n).map (· + 1)

/-- Number of permutations of length `n` sorted by `s_231` followed by `s`. -/
def sortedCount (n : ℕ) : ℕ :=
  ((idList n).permutations.filter (fun π => west (s231 π) == idList n)).length

/-- Defant's conjecture: these permutations are counted by A033321. -/
theorem main : ∀ n, sortedCount n = a n := by
  sorry

end OMA.S_oeis_a033321
