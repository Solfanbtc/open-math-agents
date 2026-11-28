import Mathlib

/-!
# A075594: a(1) = 1, a(2n) = composite, a(2n+1) = prime and sum of two successive terms is alternately prime or composite.

Source: https://oeis.org/A075594 (and https://oeis.org/A075593)
Credit: @Solfanbtc

Both sequences are greedy (as the example in A075594 and the PARI program make explicit):
`a(1) = 1`, and for `i ≥ 2`, `a(i)` is the least positive integer not among `a(1), ..., a(i-1)`
of the required kind such that `a(i-1) + a(i)` has the required kind.
Composite means `> 1` and not prime.

* A075594: `a(2n)` composite, `a(2n+1)` prime, and the sums `a(j) + a(j+1)` are prime, composite,
  prime, ... (starting with `a(1) + a(2) = 5`). So for even `i`, `a(i)` is composite with
  `a(i-1) + a(i)` prime; for odd `i ≥ 3`, `a(i)` is prime with `a(i-1) + a(i)` composite.
  Data: 1, 4, 2, 9, 3, 8, 7, 6, 19, 10, 5, ...
* A075593: `a(2n)` prime, `a(2n+1)` composite, and the sums are composite, prime, composite, ...
  (starting with `1 + 3 = 4`). So for even `i`, `a(i)` is prime with `a(i-1) + a(i)` composite;
  for odd `i ≥ 3`, `a(i)` is composite with `a(i-1) + a(i)` prime. Data: 1, 3, 4, 2, 9, 5, ...

These definitions reproduce every listed term of both entries (checked in Python). A required
term always exists (the least candidate is taken via `sInf`; the value `0` would only arise if
there were none, which does not happen in the computed range).

Conjecture (A. Murthy, A075594 %C): there are `k` and `r` with `a(n + r) = A075593(n)` for all
`n > k`. The shift `r` is taken in `ℤ` (the source does not restrict its sign); for `n > k`
with `k` large `n + r ≥ 1`, and `toNat` only matters for the finitely many small `n`, which the
choice of `k` can skip. The follow-up question (the values of `k` and `r`) is not stated.
Numerically no `|r| ≤ 15` works for `n ≤ 20000` (for `r = 1` the last mismatch is at
`n = 19975`), so the conjecture may be false.
-/

namespace OMA.S_oeis_a075594

/-- Composite: greater than 1 and not prime. -/
def Composite (m : ℕ) : Prop := 1 < m ∧ ¬ m.Prime

/-- Kind C: `m` composite and `prev + m` prime. -/
def KindC (prev m : ℕ) : Prop := Composite m ∧ (prev + m).Prime

/-- Kind P: `m` prime and `prev + m` composite. -/
def KindP (prev m : ℕ) : Prop := m.Prime ∧ Composite (prev + m)

/-- The next term of the greedy sequence after the list `L` of earlier terms; `evenC` says
whether even-indexed terms are of kind C (A075594) or of kind P (A075593). -/
noncomputable def next (evenC : Bool) (L : List ℕ) : ℕ :=
  if L = [] then 1 else
    let i := L.length + 1
    let prev := L.getLast?.getD 0
    if (Even i ↔ evenC = true) then sInf {m : ℕ | m ∉ L ∧ KindC prev m}
    else sInf {m : ℕ | m ∉ L ∧ KindP prev m}

/-- The first `n` terms. -/
noncomputable def terms (evenC : Bool) : ℕ → List ℕ
  | 0 => []
  | n + 1 => terms evenC n ++ [next evenC (terms evenC n)]

/-- A075594(n), for `n ≥ 1`. -/
noncomputable def A075594 (n : ℕ) : ℕ := ((terms true n).getLast?).getD 0

/-- A075593(n), for `n ≥ 1`. -/
noncomputable def A075593 (n : ℕ) : ℕ := ((terms false n).getLast?).getD 0

theorem main : ∃ k : ℕ, ∃ r : ℤ, ∀ n : ℕ, k < n →
    A075594 ((n : ℤ) + r).toNat = A075593 n := by
  sorry

end OMA.S_oeis_a075594
