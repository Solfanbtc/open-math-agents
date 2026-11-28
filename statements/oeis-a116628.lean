import Mathlib

/-!
# A116628: every power of 2 occurs in A116624, in ascending order

Source: https://oeis.org/A116628 (with https://oeis.org/A116624 and https://oeis.org/A116625)
A116624 (offset 1): `b(1) = 1`; for `n > 1`, `b(n)` is the least positive integer not appearing
earlier such that `{b(k) : k ≤ n}` and `{b(k) XOR b(k-1) : 2 ≤ k ≤ n}` are disjoint sets of distinct
numbers; equivalently (comment and Mathematica program of A116624), `b(n)` is the least `i`
such that neither `i` nor `i XOR b(n-1)` is among the earlier terms and earlier XORs.
Data: 1, 2, 4, 8, 5, 10, 16, 7, 9, 17, 32, ... A116625 is `b(n) XOR b(n+1)`.
A116628 lists the positions where `b` is a power of 2: 1, 2, 3, 4, 7, 11, 26, 42, ...
Conjecture of the entry: "all the powers of 2 occur in A116624 (implying that none occur in
A116625) and they occur in ascending order, in which case A116624(a(n)) = A000079(n-1)."

We state: every `2^j` occurs in `b`, and `2^j` occurs before `2^(j+1)`.

Formalization. `state n` is the pair (terms `b(1..n+1)`, all numbers used so far, i.e. the terms
and the XORs). The next term is searched in `1, ..., 2s+1` where `s` is the number of used
values: at most `2s` candidates are excluded, so the bounded search finds the true least one.
Checked with python3: the rule reproduces the 66 listed terms of A116624, and the positions of
`2^0, ..., 2^16` are the first 17 listed terms of A116628, in increasing order.

Credit: @Solfanbtc
-/

namespace OMA.S_oeis_a116628

/-- One step: append the least admissible `k` and record `k` and `k XOR last` as used. -/
def step (st : List ℕ × List ℕ) : List ℕ × List ℕ :=
  let last := st.1.getLastD 1
  let k := ((List.range' 1 (2 * st.2.length + 1)).find?
    (fun k => k ∉ st.2 ∧ (last ^^^ k) ∉ st.2)).getD 0
  (st.1 ++ [k], st.2 ++ [k, last ^^^ k])

/-- After `n` steps: the terms `b(1), ..., b(n+1)` and the used values. -/
def state (n : ℕ) : List ℕ × List ℕ := step^[n] ([1], [1])

/-- A116624 (offset 1). -/
def b (m : ℕ) : ℕ := (state (m - 1)).1.getD (m - 1) 0

theorem main :
    (∀ j : ℕ, ∃ m : ℕ, 1 ≤ m ∧ b m = 2 ^ j) ∧
    (∀ j m m' : ℕ, 1 ≤ m → 1 ≤ m' → b m = 2 ^ j → b m' = 2 ^ (j + 1) → m < m') := by
  sorry

end OMA.S_oeis_a116628
