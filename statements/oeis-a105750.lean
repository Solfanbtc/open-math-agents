import Mathlib

/-!
# A105750: the type 2 primes of Re ∏ (1 + k i) are 2 and the primes ≡ 1 (mod 4)

Source: https://oeis.org/A105750
`a(n) = Re ∏_{k=0}^{n} (1 + k i)` (offset 0): 1, 1, -1, -10, -10, 190, 730, ...
Comment of Peter Bala (Jun 03 2023), after Moll (2012), who "divided the primes into three
classes. Type 1: primes p that do not divide any element of the sequence {a(n)} ... Type 2: primes
p such that the p-adic valuation v_p(a(n)) has asymptotically linear behavior ... We conjecture
that the set of type 2 primes consists of primes p == 1 (mod 4) ... together with the prime
p = 2 ... Type 3: primes p such that the sequence of p-adic valuations {v_p(a(n)) : n >= 0}
exhibits an oscillatory behavior (this phrase is not precisely defined). We conjecture that the
sets of type 1 and type 3 primes taken together consist of primes p == 3 (mod 4)."

Formalization.
* "Asymptotically linear behavior" is read as `v_p(a(n)) ~ c n` for some constant `c > 0`, i.e.
  `v_p(a(n)) / n → c > 0` (the form of Moll's conjecture 5.5, `v_p ~ n/(p-1)`, as in upstream
  `OeisA105751.conjecture.variants.moll_p_mod_4_eq_1` for the imaginary part). Slope 0 is
  excluded, since type 1 primes (`v_p = 0` throughout) are a different class.
* We state the type 2 conjecture: a prime `p` is of type 2 iff `p = 2` or `p ≡ 1 (mod 4)`.
  Type 3 is "not precisely defined"; reading the three types as a partition of the primes, the
  second conjecture (types 1 and 3 together are the primes `≡ 3 (mod 4)`) is the same statement
  for the complementary set, so it is not stated separately.
* `a n` is computed in the Gaussian integers `ℤ[i]` (`⟨1, k⟩ = 1 + k i`); `padicValInt p 0 = 0`
  (no term `a(n)` with `n ≤ 3000` vanishes).
Checked with python3: the 23 listed terms; for `n = 3000`, `v_p(a(n))/n` is 0.25 for `p = 2, 5`,
0.083 for 13, 0.062 for 17 (`≈ 1/(p-1)`), while for `p = 3, 7, 11, 19, 23, 43` the valuation
stays `≤ 4` for all `n ≤ 3000`.

Credit: @Solfanbtc
-/

namespace OMA.S_oeis_a105750

open Filter Topology

/-- A105750: `a(n) = Re ∏_{k=0}^{n} (1 + k i)`. -/
def a (n : ℕ) : ℤ := (∏ k ∈ Finset.range (n + 1), (⟨1, k⟩ : GaussianInt)).re

/-- `p` is a type 2 prime: `v_p(a(n))` grows asymptotically linearly, `v_p(a(n)) / n → c > 0`. -/
def IsType2 (p : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ Tendsto (fun n : ℕ => (padicValInt p (a n) : ℝ) / n) atTop (𝓝 c)

theorem main : ∀ p : ℕ, p.Prime → (IsType2 p ↔ p = 2 ∨ p % 4 = 1) := by
  sorry

end OMA.S_oeis_a105750
