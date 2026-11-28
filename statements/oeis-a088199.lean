import Mathlib

/-!
# A088199: Primes where the difference sequence A088197 of LQnR(p_n) is ≤ 0.

Source: https://oeis.org/A088199
Credit: @Solfanbtc

`LQnR(p)` (A088196, `p` an odd prime) is the largest quadratic non-residue modulo `p`: the
largest `x ∈ [1, p-1]` that is not a square mod `p`. A088197 is its first-difference sequence,
`A088197(n) = LQnR(p_{n+1}) - LQnR(p_n)` (`n ≥ 2`, `p_n` the `n`-th prime). A088199 lists the
primes `p_{n+1}` for which this difference is `≤ 0`: `73` (`LQnR(73) = 68 ≤ 70 = LQnR(71)`),
`193`, `241`, …. Checked with python3: this reading reproduces the 15 listed terms.
With `Nat.nth Nat.Prime` (0-indexed) the pair is `q = Nat.nth Nat.Prime k`,
`p = Nat.nth Nat.Prime (k+1)` with `k ≥ 1` (`q ≥ 3`).

Conjecture (entry): the members are always `≡ 1 (mod 8)`. (Remark: this has an elementary
proof. If `p ≡ 3 (mod 4)` then `-1` is a non-residue and `LQnR(p) = p - 1`. If `p ≡ 5 (mod 8)`
then `-1` is a residue and `-2` is not, so `LQnR(p) = p - 2`. In both cases
`LQnR(p) > q - 1 ≥ LQnR(q)` for the previous prime `q ≤ p - 2`. It is stated here as the
entry states it.)
-/

namespace OMA.S_oeis_a088199

/-- A088196: the largest quadratic non-residue modulo `p` in `[1, p-1]`, i.e. the largest
`x ∈ [1, p-1]` with `y^2 mod p ≠ x` for all `y < p` (`0` if there is none). -/
def lqnr (p : ℕ) : ℕ :=
  ((Finset.Ico 1 p).filter (fun x => ∀ y ∈ Finset.range p, y * y % p ≠ x)).sup id

/-- The conjecture: if `LQnR(p_{n+1}) ≤ LQnR(p_n)` (`n ≥ 2`), then `p_{n+1} ≡ 1 (mod 8)`. -/
theorem main : ∀ k : ℕ, 1 ≤ k →
    lqnr (Nat.nth Nat.Prime (k + 1)) ≤ lqnr (Nat.nth Nat.Prime k) →
    Nat.nth Nat.Prime (k + 1) % 8 = 1 := by
  sorry

end OMA.S_oeis_a088199
