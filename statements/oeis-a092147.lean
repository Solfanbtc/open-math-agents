import Mathlib

/-!
# A092147: Number of even-length palindromes among the k-tuples of partial quotients of the continued fraction expansions of n/r, r=1,...,n.

Source: https://oeis.org/A092147
Credit: @Solfanbtc

For `1 ≤ r ≤ n`, the continued fraction of `n/r` is the list of Euclidean quotients
`cfq n r = [a_0, a_1, …, a_k]`. Every rational also has the second expansion
`[a_0, …, a_{k-1}, a_k - 1, 1]` (`alt`). `a(n)` counts the `r` such that one of the two expansions
is a palindrome of even length. Both expansions are needed to match the data: `a(2) = 1` comes
from `2/1 = [1; 1]`, and `a(5) = 2` from `5/2 = [2; 2]` and `5/3 = [1; 1, 1, 1]`. Checked with
python3: this reproduces the 68 listed terms 0, 1, 0, 1, 2, 1, 0, 1, 0, 5, ..., and agrees with
R. Oudra's formula `a(n) = #{1 ≤ k < n : k (n - k) is a square}` for `n < 300`.

Conjecture (J. W. Layman): let `n = 2^r p^s` with `p` an odd prime and `s > 0`. If `p ≡ 1 (mod 4)`,
then `a(n) = 2s` for `r = 0` and `a(n) = 4s + 1` for `r > 0`. If `p ≡ 3 (mod 4)`, then
`a(n) = 0` for `r = 0` and `a(n) = 1` for `r > 0`. Finally, if `n = 2^r`, then `a(n) = 1`.
Range fix: the last clause fails at `n = 1 = 2^0` (`a(1) = 0`), so `main` requires `r ≥ 1` there.
(python3: with this fix the conjecture holds for all `n < 3000`.)
Status: proved, as a special case of J. E. Shockley's theorem (2004) in the entry, which gives
`a(n)` for all `n` in terms of the exponents of the primes `≡ 1 (mod 4)`.
-/

namespace OMA.S_oeis_a092147

/-- Euclidean quotients of `a / b`, with fuel `f`. -/
def cfq : ℕ → ℕ → ℕ → List ℕ
  | 0, _, _ => []
  | f + 1, a, b => if b = 0 then [] else (a / b) :: cfq f b (a % b)

/-- The continued fraction `[a_0; a_1, …, a_k]` of `n / r` (fuel `n + r` suffices). -/
def cf (n r : ℕ) : List ℕ := cfq (n + r) n r

/-- The other expansion `[a_0; …, a_{k-1}, a_k - 1, 1]`. -/
def alt (l : List ℕ) : List ℕ := l.dropLast ++ [l.getLastD 0 - 1, 1]

/-- `l` is a palindrome of even length. -/
def EvenPal (l : List ℕ) : Prop := Even l.length ∧ l.reverse = l

open Classical in
/-- A092147(n). -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (fun r => EvenPal (cf n r) ∨ EvenPal (alt (cf n r)))).card

theorem main :
    (∀ r s p : ℕ, p.Prime → p % 4 = 1 → 0 < s →
      a (2 ^ r * p ^ s) = if r = 0 then 2 * s else 4 * s + 1) ∧
    (∀ r s p : ℕ, p.Prime → p % 4 = 3 → 0 < s →
      a (2 ^ r * p ^ s) = if r = 0 then 0 else 1) ∧
    (∀ r : ℕ, 1 ≤ r → a (2 ^ r) = 1) := by
  sorry

end OMA.S_oeis_a092147
