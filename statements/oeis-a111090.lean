import Mathlib

/-!
# A111090: Successive generations of an alternating Kolakoski rule.

Source: https://oeis.org/A111090
Credit: @Solfanbtc

Conjecture (Benoit Cloitre, OEIS A111090, %F line): `a(n)` is asymptotic to `c * (3/2)^n` for
some `c`.

The sequence: `a(1) = 1`, and `a(n+1)` is obtained from the word `a(n)` (digits 1 and 2) by the
Kolakoski substitution, writing for its `i`-th digit `d` a run of `d` equal symbols, the runs
alternating between 1 and 2, with the additional rule that the first run consists of 1s if
`a(n)` begins with 2, and of 2s if `a(n)` begins with 1:
`1 → 2 → 11 → 21 → 112 → 2122 → ...`.

Reading of the conjecture. Taken literally as integers, `a(n)` has about `c (3/2)^n` decimal
digits, so it grows doubly exponentially and cannot be `~ c (3/2)^n`; the evident meaning (the
growth rate `3/2` is the mean of the run lengths 1 and 2) is that the *length* of the word
`a(n)` is asymptotic to `c (3/2)^n`. That is what is stated, with `c > 0` (implicit in `~`).

Formalization.
* Words are `List ℕ`; `gen k` is `a(k + 1)` (so `gen 0 = [1]`); the index shift only changes
  the constant `c`.
* The other %F claim (`a(2n-1)` and `a(2n)` converge to A025142 and A025143) is not stated as a
  conjecture in the source and is not part of this statement.

Checked with python3 and `#eval`: `gen` reproduces all listed %S/%T terms (11 words), and
`length (gen n) / (3/2)^n ≈ 0.6141` for `30 ≤ n ≤ 45`.
-/

namespace OMA.S_oeis_a111090

open Asymptotics Filter

/-- One generation of the alternating Kolakoski rule. -/
def subst (w : List ℕ) : List ℕ :=
  let s := if w.head? = some 1 then 2 else 1
  (w.mapIdx (fun i d => List.replicate d (if i % 2 = 0 then s else 3 - s))).flatten

/-- `gen k` is the word `a(k + 1)` of A111090. -/
def gen : ℕ → List ℕ
  | 0 => [1]
  | k + 1 => subst (gen k)

/-- The length of `a(n)` is asymptotic to `c (3/2)^n` for some `c > 0`. -/
theorem main : ∃ c : ℝ, 0 < c ∧
    IsEquivalent atTop (fun n : ℕ => ((gen n).length : ℝ)) (fun n : ℕ => c * (3 / 2 : ℝ) ^ n) := by
  sorry

end OMA.S_oeis_a111090
