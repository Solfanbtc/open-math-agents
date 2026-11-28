import Mathlib

/-!
# A078623: matched parentheses and brackets where a closing bracket closes open parentheses.

Source: https://oeis.org/A078623
Credit: @Solfanbtc

A078623(n) is the number of strings of length `n` over `( ) [ ]` that are matched when a
closing bracket `]` also closes every parenthesis still open back to its matching `[`
(as in some versions of LISP). Here a string `w : Fin n → Fin 4` is coded as
`0 = (`, `1 = )`, `2 = [`, `3 = ]`, and is read left to right with a stack of open symbols
(`false = (`, `true = [`). `(` and `[` push. `)` pops a `(` that must be on top. `]` pops every
`(` on top and then the `[` under them, which must exist. The string is valid when this never
fails and the stack ends empty. Checked with python3: this gives `1, 0, 2, 1, 9, 11, 56, 106,
421, 1009, 3565` for `n = 0..10` (the entry's data; e.g. `a(5) = 11`, the strings listed in the
example).

Conjecture (Peter Bala, 2015): for `n ≥ 1`,
`a(n-1) = (-1)^(n-1) * (1/n) * Σ_{k=1}^n binomial(n, k) * binomial(n - 2k, k - 1)`,
where `binomial(n - 2k, k - 1)` has a possibly negative upper argument, i.e. the generalized
binomial coefficient `x (x-1) ⋯ (x-j+1) / j!` (`Ring.choose` on `ℤ`). Checked with python3
against the 30 listed terms (`n = 1..30`).
-/

namespace OMA.S_oeis_a078623

/-- Pop the open parentheses on top of the stack, then the bracket under them. -/
def closeBracket : List Bool → Option (List Bool)
  | [] => none
  | false :: s => closeBracket s
  | true :: s => some s

/-- Read one symbol (`0 = (`, `1 = )`, `2 = [`, `3 = ]`). -/
def readSym : Option (List Bool) → Fin 4 → Option (List Bool)
  | none, _ => none
  | some s, c =>
    if c = 0 then some (false :: s)
    else if c = 1 then (match s with
      | false :: t => some t
      | _ => none)
    else if c = 2 then some (true :: s)
    else closeBracket s

/-- The string is matched (LISP convention). -/
def valid {n : ℕ} (w : Fin n → Fin 4) : Bool :=
  (List.ofFn w).foldl readSym (some []) == some []

/-- A078623(n). -/
def a (n : ℕ) : ℕ := (Finset.univ.filter fun w : Fin n → Fin 4 => valid w = true).card

/-- Peter Bala's conjectured formula. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    (a (n - 1) : ℚ) = (-1) ^ (n - 1) * (1 / (n : ℚ)) *
      ∑ k ∈ Finset.Icc 1 n, (n.choose k : ℚ) * (Ring.choose ((n : ℤ) - 2 * k) (k - 1) : ℚ) := by
  sorry

end OMA.S_oeis_a078623
