import Mathlib

/-!
# A003989: Triangle T from the array A(x, y) = gcd(x,y), for x >= 1, y >= 1, read by antidiagonals.

Source: https://oeis.org/A003989
Credit: @Solfanbtc

Conjecture (Jason Richardson-White, May 06 2013): take a torus whose cross-section is a regular
polygon with `m` sides, break it, twist the free ends by `n` faces (preserving rotational
symmetry) and reattach them (`m > 1`, `n > 0`). The number of independent closed paths on the
surface of the resulting torus is always `gcd(m, n)`.

Combinatorial model (the reading of the comment, made explicit). Number the `m` longitudinal
faces (strips) of the torus `0, ..., m - 1` around the cross-section. A path running along the
surface in the long direction stays in one strip on each trip around the torus, and the twist
by `n` faces carries strip `i` to strip `(i + n) mod m` when the path passes the reattachment.
So a closed path visits exactly the strips `(i + k * n) mod m`, `k ≥ 0` (it is closed after
finitely many trips because there are finitely many strips), and two paths are the same
(not independent) when they visit the same strips. The independent closed paths are therefore
the orbits of `i ↦ (i + n) mod m` on `{0, ..., m - 1}`; since the orbit has period dividing `m`,
the orbit of `i` is `{(i + k * n) mod m | k < m}`.
-/

namespace OMA.S_oeis_a003989

/-- The strips visited by the closed path starting in strip `i`, for a twist of `n` faces on a
torus with `m`-gonal cross-section. -/
def path (m n i : ℕ) : Finset ℕ :=
  (Finset.range m).image (fun k => (i + k * n) % m)

/-- The independent closed paths: the distinct strip sets of paths starting in each strip. -/
def paths (m n : ℕ) : Finset (Finset ℕ) :=
  (Finset.range m).image (path m n)

/-- Richardson-White's conjecture: the number of independent closed paths is `gcd(m, n)`. -/
theorem main : ∀ m n : ℕ, 1 < m → 0 < n → (paths m n).card = Nat.gcd m n := by
  sorry

end OMA.S_oeis_a003989
