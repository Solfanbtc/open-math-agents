import Mathlib

/-!
# A107267: A square array of Motzkin related transforms, read by antidiagonals.

Source: https://oeis.org/A107267
Credit: @Solfanbtc

Conjecture (entry comment, Paul Barry): "rows count weighted Motzkin paths". The entry makes it
precise in a later comment by the same author (May 16 2005): "Row k counts colored Motzkin
paths, where H(1,0) and U(1,1) each have k colors and D(1,-1) one color." We state this precise
form (the earlier sentence names no weights, so it has no other precise reading in the entry).

Definitions.
* The array (formula section): T(k, m) = Sum_{j=0..m} k^j * C(m,j) * C(j+1, m-j+1)/(j+1),
  row `k ≥ 0` (number of colours), column `m ≥ 0` (path length); computed in `ℚ`. Read by
  antidiagonals T(0,d), T(1,d-1), ..., T(d,0), this reproduces all 66 data terms (`#eval`).
* A Motzkin path of length `m` is a word in U = 2, H = 1, D = 0 (`Fin 3`, step value `s - 1`)
  whose partial heights never go below 0 and which ends at height 0. With k colours on each U
  and each H step and one colour on D, the number of coloured paths is the sum over Motzkin
  paths of `k^(#U + #H)`.
* Statement: for all `k, m`, the number of coloured Motzkin paths of length `m` equals T(k, m).
  (For k = 0, 0^0 = 1 makes the empty path the only one counted, matching row 0 = 1, 0, 0, ...)
  Checked with `#eval` for k ≤ 4, m ≤ 6. Barry's comment presents the precise form as a fact;
  grouping paths by their number u of U steps (C(m,2u) Catalan(u) paths of weight k^(m-u))
  gives Seiichi Manyama's formula in the entry, so this is expected to be an elementary identity.
-/

namespace OMA.S_oeis_a107267

/-- The array A107267, row `k`, column `m`. -/
def T (k m : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (m + 1),
    (k : ℚ) ^ j * (m.choose j : ℚ) * ((j + 1).choose (m - j + 1) : ℚ) / (j + 1)

/-- Height after the first `i` steps (step `s` has value `s - 1`). -/
def height {m : ℕ} (w : Fin m → Fin 3) (i : ℕ) : ℤ :=
  ∑ t : Fin m, if t.val < i then ((w t : ℕ) : ℤ) - 1 else 0

/-- `w` is a Motzkin path. -/
def IsMotzkin {m : ℕ} (w : Fin m → Fin 3) : Prop :=
  (∀ i ≤ m, 0 ≤ height w i) ∧ height w m = 0

instance {m : ℕ} : DecidablePred (@IsMotzkin m) := fun w => by unfold IsMotzkin; infer_instance

/-- Number of Motzkin paths of length `m` with `k` colours on U and H steps, one on D. -/
def colored (k m : ℕ) : ℕ :=
  ∑ w ∈ (Finset.univ : Finset (Fin m → Fin 3)).filter IsMotzkin,
    k ^ (Finset.univ.filter fun t => w t ≠ 0).card

theorem main : ∀ k m : ℕ, (colored k m : ℚ) = T k m := by
  sorry

end OMA.S_oeis_a107267
