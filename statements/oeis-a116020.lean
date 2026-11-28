import Mathlib

/-!
# A116020: Numbers n such that sigma(n) - phi(n) is a repdigit greater than 2.

Source: https://oeis.org/A116020
Credit: @Solfanbtc

Claim (Farideh Firoozbakht, Aug 24 2006, comment (I) in A116020): if both `p = 4*10^n + 1` and
`q = (4*10^n - 13)/9` are primes then `m = p*q` is in the sequence, because
`σ(m) - φ(m) = 8*(10^(n+1) - 1)/9` is a repdigit. Conjecture: `123`, `17243` and `1772443` are
all such terms.

Reading. `123 = 41 * 3`, `17243 = 401 * 43` and `1772443 = 4001 * 443` are the terms for
`n = 1, 2, 3`; since `m = p q` determines `n` (it is increasing in `n`), "these are all such
terms" says exactly that `p` and `q` are both prime only for `n ∈ {1, 2, 3}`.

Formalization.
* `n ≥ 1` (for `n = 0`, `q` would be negative); then `9 ∣ 4*10^n - 13`, as `4*10^n ≡ 4 ≡ 13`
  mod 9, so the division is exact.

Checked with python3: `σ(n) - φ(n)` a repdigit `> 2` gives exactly the listed %S/%T/%U terms up
to 26483, and `p`, `q` are both (probable) primes for `1 ≤ n < 800` only at `n = 1, 2, 3`, where
`σ(m) - φ(m) = 88, 888, 8888`.
-/

namespace OMA.S_oeis_a116020

/-- `4*10^n + 1` and `(4*10^n - 13)/9` are both prime exactly for `n = 1, 2, 3`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    ((4 * 10 ^ n + 1).Prime ∧ ((4 * 10 ^ n - 13) / 9).Prime ↔ n = 1 ∨ n = 2 ∨ n = 3) := by
  sorry

end OMA.S_oeis_a116020
