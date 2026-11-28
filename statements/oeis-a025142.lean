import Mathlib

/-!
# A025142: Fixed point of the square runlength transform, with a(1) = 1

Source: https://oeis.org/A025142
Credit: @Solfanbtc

For a sequence `s` of 1's and 2's, the run-length transform `RL(s)` is the sequence of the lengths
of the successive runs of equal symbols of `s`. A025142 is the unique sequence `a` of 1's and 2's
with `a(1) = 1` and `RL²(a) = a ≠ RL(a)`; `b = RL(a)` is A025143, and `a = RL(b)`:
`a = 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, ...`, `b = 2, 1, 2, 2, 1, 2, 1, 1, 2, 2, ...` (offset 1).

Conjecture (Jean-Christophe Hervé, Oct 21 2014, in the entry): as for the Kolakoski sequence, the
limiting frequency of 1's (and of 2's) in this sequence is 1/2. Stated as:
`#{n ≤ N : a(n) = 1} / N → 1/2`.

The sequence is characterized, not constructed: the statement quantifies over all pairs `(a, b)`
of 1/2-sequences with `a(1) = 1`, `b` the run lengths of `a`, `a` the run lengths of `b`, and
`a ≠ b`; by the entry this pair exists and is unique (A025142, A025143).

A python3 check: the construction reproduces the data, and the frequency of 1's among the first
`10³, 10⁴, 10⁵, 10⁶` terms is `0.5, 0.4993, 0.50002, 0.5000005`.

Conventions:
* Sequences are `ℕ → ℕ`, indexed from 1.
* `RunLengths s r`: there are run starts `1 = q 1 < q 2 < ...` with `q (k+1) = q k + r k`, `s`
  constant on `[q k, q (k+1))`, and `s (q (k+1)) ≠ s (q k)`; then `r k` is the length of the `k`-th
  run of `s`.
-/

namespace OMA.S_oeis_a025142

open Filter Topology

/-- `r` is the run-length sequence of `s` (both indexed from 1). -/
def RunLengths (s r : ℕ → ℕ) : Prop :=
  ∃ q : ℕ → ℕ, q 1 = 1 ∧ ∀ k : ℕ, 1 ≤ k →
    1 ≤ r k ∧ q (k + 1) = q k + r k ∧ (∀ j, q k ≤ j → j < q (k + 1) → s j = s (q k)) ∧
      s (q (k + 1)) ≠ s (q k)

/-- Hervé's conjecture: the frequency of 1's in A025142 tends to 1/2. -/
theorem main : ∀ a b : ℕ → ℕ,
    (∀ n, 1 ≤ n → a n = 1 ∨ a n = 2) → (∀ n, 1 ≤ n → b n = 1 ∨ b n = 2) →
    a 1 = 1 → RunLengths a b → RunLengths b a → (∃ n, 1 ≤ n ∧ a n ≠ b n) →
    Tendsto (fun N : ℕ => (((Finset.Icc 1 N).filter (fun n => a n = 1)).card : ℝ) / N)
      atTop (𝓝 (1 / 2)) := by
  sorry

end OMA.S_oeis_a025142
