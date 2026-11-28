import Mathlib

/-!
# A371761: Array read by antidiagonals: The number of parades with n girls and k boys that begin with a girl and end with a boy.

Source: https://oeis.org/A371761
Credit: @Solfanbtc

Conjecture (OEIS A371761, comment; also in A136301, Peter Luschny, Apr 10 2024):
Row n + 1 is row 2^n in table A136301.

Definitions:
* A371761(n, k) (Knuth's girls and boys parades): girls g_1 < ... < g_n and boys
  b_1 < ... < b_k (by age) line up so that no girl is directly preceded by an older girl and
  no boy is directly preceded by an older boy; A(n, k) counts the lineups that begin with a
  girl and end with a boy. Here the persons are `Fin (n + k)`, the girls are `0, ..., n-1`
  and the boys are `n, ..., n+k-1`, both ordered by age as by index. A lineup is a
  permutation `f` (`f t` is the person at position `t`). Checked in Python by brute force: this
  gives the rows n = 1, ..., 4 of the array (0, 1, 1, 1, ...; 0, 1, 5, 13, 29, ...;
  0, 1, 13, 73, 301, ...; 0, 1, 29, 301, 2069). Only rows n + 1 >= 1 occur in the conjecture.
* A136301 is written as columns j = 1, 2, ..., column j having rows r = 1, ..., 2^(j-1)
  (see its Example section). The entry defines the frequencies through the Secret Santa
  patterns and computes them with the Mathematica program in the entry; `santa` transcribes
  that program: `santa i r` is `sFreq[[i, r]]`, and the entry in column j, row r of A136301
  is `santa (j + 1) r`. In the program, rows `i = p + 2` (p >= 1) are filled block by block:
  for 1 <= s <= p and 1 <= t <= 2^(s-1),
  `sFreq[[p+2, 2^(s-1)+t]] = Sum_{q=0..p+1-s} pasc(p+1-s, q) * sFreq[[s+q, t]]` with
  `pasc(P, q) = binomial(P+1, q) - [q >= P]`, `sFreq[[i, 1]] = 1` for i >= 2, and all
  other entries 0. Checked in Python: this reproduces the first 75 terms of A136301.
* Row 2^n of A136301 consists of the entries of the columns j >= n + 1 (shorter columns
  have no row 2^n); column j = n + k, k = 1, 2, ..., is compared with A(n + 1, k).
  (The term A(n + 1, 0) = 0 has no counterpart in A136301.) Checked in Python for
  n <= 5 and all k with n + k <= 12.
-/

namespace OMA.S_oeis_a371761

/-- `f` is a parade of `n` girls (persons `0..n-1`) and `k` boys (persons `n..n+k-1`) that
begins with a girl and ends with a boy. -/
def IsParade (n k : ℕ) (f : Equiv.Perm (Fin (n + k))) : Prop :=
  (∀ t u : Fin (n + k), u.val = t.val + 1 →
      (((f t).val < n ∧ (f u).val < n) ∨ (n ≤ (f t).val ∧ n ≤ (f u).val)) → f t < f u) ∧
  (∀ t : Fin (n + k), t.val = 0 → (f t).val < n) ∧
  (∀ t : Fin (n + k), t.val + 1 = n + k → n ≤ (f t).val)

instance (n k : ℕ) (f : Equiv.Perm (Fin (n + k))) : Decidable (IsParade n k f) := by
  unfold IsParade; infer_instance

/-- A371761(n, k): the number of such parades. -/
def parades (n k : ℕ) : ℕ :=
  (Finset.univ.filter fun f : Equiv.Perm (Fin (n + k)) => IsParade n k f).card

/-- The coefficients `pasc(P, q) = binomial(P+1, q) - [q ≥ P]` of the A136301 program. -/
def pasc (P q : ℕ) : ℕ := Nat.choose (P + 1) q - if P ≤ q then 1 else 0

/-- `santa i r = sFreq[[i, r]]` of the Mathematica program of A136301; the entry in column
`j`, row `r` of A136301 is `santa (j + 1) r`. -/
def santa (i r : ℕ) : ℕ :=
  if i ≤ 1 ∨ r = 0 then 0
  else if i = 2 then (if r = 1 then 1 else 0)
  else if r = 1 then 1
  else if 2 ^ (i - 2) < r then 0
  else
    ∑ q : Fin (i - (Nat.log 2 (r - 1) + 1)),
      pasc (i - 1 - (Nat.log 2 (r - 1) + 1)) q *
        santa ((Nat.log 2 (r - 1) + 1) + q) (r - 2 ^ Nat.log 2 (r - 1))
termination_by i
decreasing_by omega

/-- Conjecture: row `n + 1` of A371761 is row `2 ^ n` of A136301: for every `k ≥ 1`, the
entry of A136301 in column `n + k`, row `2 ^ n` equals `A371761(n + 1, k)`. -/
theorem main : ∀ n k : ℕ, 1 ≤ k → santa (n + k + 1) (2 ^ n) = parades (n + 1) k := by
  sorry

end OMA.S_oeis_a371761
