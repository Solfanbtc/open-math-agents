import Mathlib

/-!
# A026465: Length of n-th run of identical symbols in the Thue-Morse sequence A010060.

Source: https://oeis.org/A026465
Credit: @Solfanbtc

John W. Layman's conjecture (1) (Feb 18 2003, in the entry): the sequence can be calculated by
starting with 1 and repeatedly replacing 1 with 1, 2, 1 and 2 with 1, 2, 2, 2, 1; i.e. it is the
fixed point of the morphism alpha: 1 -> 121, 2 -> 12221 starting with 1.

Status: PROVED by Michel Dekking (Feb 13 2019, comment in the entry): tau^2 (tau the Thue-Morse
morphism 0 -> 01, 1 -> 10) maps consecutive runs to consecutive runs, a run of length 1 to runs
of lengths 1,2,1 and a run of length 2 to runs of lengths 1,2,2,2,1. Layman's characterizations
(2) and (3) and Povolotsky's palindrome conjecture follow from (1), as noted in the entry.

Conventions.
* `t i` is A010060 (offset 0): parity of the binary digit sum of `i`.
* `e k` is the k-th (0-indexed) position `i` with `t i ≠ t (i+1)`, i.e. the last position of
  the (k+1)-th run. The runs are `[0, e 0]`, `[e 0 + 1, e 1]`, ..., so with offset 1 (as in the
  entry): `a 1 = e 0 + 1` and `a (k+2) = e (k+1) - e k`. (Checked: a(1..6) = 1,2,1,1,2,2.)
* "Start with 1 and repeatedly replace" is stated as: for every k, the word `alpha^k(1)` is a
  prefix of `a(1), a(2), ...` (these words have unbounded length, so they determine the whole
  sequence). Checked numerically for k ≤ 6 (2731 terms).
-/

namespace OMA.S_oeis_a026465

/-- The Thue-Morse sequence A010060. -/
def t (i : ℕ) : ℕ := (Nat.digits 2 i).sum % 2

/-- The k-th (0-indexed) end position of a run of `t`. -/
noncomputable def e (k : ℕ) : ℕ := Nat.nth (fun i => t i ≠ t (i + 1)) k

/-- A026465 (offset 1): length of the n-th run of `t`. -/
noncomputable def a : ℕ → ℕ
  | 0 => 0
  | 1 => e 0 + 1
  | k + 2 => e (k + 1) - e k

/-- The morphism 1 -> 121, 2 -> 12221. -/
def alpha : ℕ → List ℕ
  | 1 => [1, 2, 1]
  | 2 => [1, 2, 2, 2, 1]
  | _ => []

/-- `alpha^k` applied to the word `1`. -/
def W : ℕ → List ℕ
  | 0 => [1]
  | k + 1 => (W k).flatMap alpha

theorem main : ∀ (k i : ℕ) (h : i < (W k).length), a (i + 1) = (W k)[i] := by
  sorry

end OMA.S_oeis_a026465
