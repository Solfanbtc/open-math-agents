import Mathlib

/-!
# A123710: rows of the inverse of ⌊n/k⌋ with exactly 4 nonzero entries

Source: https://oeis.org/A123710 (with https://oeis.org/A123706 and https://oeis.org/A123709)
A123706 is the matrix inverse of the lower triangular matrix A010766, `[n/k]` for `n ≥ k ≥ 1`;
A123709(n) is the number of nonzero terms in row `n` of A123706; A123710 lists the `k` with
A123709(k) = 4: 4, 6, 8, 9, 16, 25, 27, 32, 49, ...
Comment and formula (M. F. Hasler, Feb 12 2012): "Except for a(2)=6, these are proper prime
powers, i.e., numbers p^k where k>1, p prime (A025475)", "a(n) = A025475(n) for n>2
(conjectured)".

We state the conjecture: for every `n ≥ 1`, row `n` of A123706 has exactly 4 nonzero entries iff
`n = 6` or `n = p^e` with `p` prime and `e ≥ 2`. (A025475 also contains 1, but A123709(1) = 1,
and the listed terms show that A123710 is `{6}` together with the proper prime powers, so the
conjecture is read as this set equality.)

Formalization. For `N = n + 1`, `D N` is the `N × N` matrix `⌊(r+1)/(c+1)⌋` (zero above the
diagonal); it is lower unitriangular, so the truncation of the inverse is the inverse of the
truncation, and row `n + 1` of A123706 is row `Fin.last n` of `(D (n+1))⁻¹`.
Checked with python3: the inverse agrees with `T(n,k) = μ(n/k) - μ(n/(k+1))` for `n ≤ 30`
(exact fractions); with that formula, the `n ≤ 9409` with 4 nonzero entries are exactly the 52
listed terms, and the conjectured characterization holds for all `n < 10^4`.

Credit: @Solfanbtc
-/

namespace OMA.S_oeis_a123710

/-- The `N × N` truncation of A010766, `⌊n/k⌋` for `n ≥ k` (0-indexed rows and columns). -/
def D (N : ℕ) : Matrix (Fin N) (Fin N) ℚ := fun r c =>
  if (c : ℕ) ≤ r then (((r : ℕ) + 1) / ((c : ℕ) + 1) : ℕ) else 0

/-- A123709(n+1): the number of nonzero entries in row `n+1` of A123706. -/
noncomputable def nonzeros (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun k : Fin (n + 1) => (D (n + 1))⁻¹ (Fin.last n) k ≠ 0)).card

theorem main : ∀ n : ℕ,
    (nonzeros n = 4 ↔ n + 1 = 6 ∨ ∃ p e : ℕ, p.Prime ∧ 2 ≤ e ∧ n + 1 = p ^ e) := by
  sorry

end OMA.S_oeis_a123710
