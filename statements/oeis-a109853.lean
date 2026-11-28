import Mathlib

/-!
# A109853: a(n) = A109852(2^n).

Source: https://oeis.org/A109853
Credit: @Solfanbtc

Conjectures (OEIS A109853, %C lines; the second and third by Robert G. Wilson v, Jun 14 2006):
1. `a(n)` is prime if `n` is not `0` nor `2`;
2. `a(n)` is the `(2n-2)`-nd prime for `n > 2`;
3. the union of the values `A109852(2^n - 1)` and `A109852(2^n)` is A046022
   `= {1, 2, 3, 4, 5, 7, 11, 13, ...}`, which except for `4` equals A008578, the noncomposite
   numbers; i.e. the union is `{1, 4} ∪ {primes}`.

A109852: `a(1) = 1`, `a(2) = 2`; for `n ≥ 1` and `1 ≤ k < 2^n`, `a(2^n + k)` is the least
multiple of `a(2^n - k)` not included earlier, and `a(2^n)` is the least number not included
earlier.

Formalization.
* `step l n` computes `A109852(n)` (`n ≥ 3`) from `l = [A109852(1), ..., A109852(n-1)]`: with
  `k = n - 2^⌊log₂ n⌋` and `t = 1` if `k = 0`, else `t = A109852(n - 2k)`, it returns the first
  of `2t, 3t, ..., (|l| + 2) t` not in `l`. This is the least unused proper multiple of `t`
  (the number `t` itself is already used: it is an earlier term, or `t = 1`): those `|l| + 1`
  candidates are distinct and at most `|l|` of them are used, so the search never fails, and
  for `k = 0` it returns the least unused number (`1` is used), as in the Maple program.
* `A n` is A109852(n) for `n ≥ 1`. The `2^n - 1` values in conjecture 3 are taken for `n ≥ 1`
  (`2^0 - 1 = 0` is not an index; `A109852(2^0) = 1 = A109852(2^1 - 1)` is included anyway).
* "The `m`-th prime" is `Nat.nth Nat.Prime (m - 1)`.
* The three conjectures are joined by `∧` (2 implies 1 for `n > 2`).

Checked with python3: the definition reproduces the listed terms of A109852 and the terms
`a(0..17)` of A109853, and all three conjectures hold for `n ≤ 17`.
-/

namespace OMA.S_oeis_a109853

/-- `A109852(n)` for `n ≥ 3`, from the list of the earlier terms `[A109852(1), ..., A109852(n-1)]`. -/
def step (l : List ℕ) (n : ℕ) : ℕ :=
  let k := n - 2 ^ Nat.log 2 n
  let t := if k = 0 then 1 else l.getD (n - 2 * k - 1) 0
  (((List.range' 2 (l.length + 1)).map (· * t)).find? (fun x => !(l.contains x))).getD 0

/-- `seqList n = [A109852(1), ..., A109852(n)]`. -/
def seqList : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | 2 => [1, 2]
  | n + 3 => seqList (n + 2) ++ [step (seqList (n + 2)) (n + 3)]

/-- A109852(n), for `n ≥ 1`. -/
def A (n : ℕ) : ℕ := (seqList n).getD (n - 1) 0

/-- A109853(n) = A109852(2^n). -/
def a (n : ℕ) : ℕ := A (2 ^ n)

/-- The three conjectures of A109853. -/
theorem main :
    (∀ n : ℕ, n ≠ 0 → n ≠ 2 → (a n).Prime) ∧
    (∀ n : ℕ, 2 < n → a n = Nat.nth Nat.Prime (2 * n - 3)) ∧
    {x : ℕ | ∃ n : ℕ, 1 ≤ n ∧ (x = A (2 ^ n - 1) ∨ x = A (2 ^ n))} =
      {x : ℕ | x = 1 ∨ x = 4 ∨ x.Prime} := by
  sorry

end OMA.S_oeis_a109853
