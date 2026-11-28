import Mathlib

/-!
# A085807: Permanent of the symmetric n X n matrix A defined by A[i,j] = |i-j| for 1 <= i,j <= n.

Source: https://oeis.org/A085807
Credit: @Solfanbtc

`a(n) = perm(|i - j|)_{1 ≤ i, j ≤ n}` (`a(0) = 1`, the empty permanent). Indices are shifted
to `Fin n`, which does not change `|i - j|`. Python (Ryser's formula) reproduces the data for
`n ≤ 9`.

Conjectures in the entry:
1. (Zhi-Wei Sun, Aug 30 2021) for every odd prime `p`, `a(p) ≡ -1/2 (mod p)`, i.e.
   `2 a(p) ≡ -1 (mod p)` (`2` is invertible mod an odd prime). Holds for `p ≤ 17` by the data.
2. (Stefano Spezia, Jul 05 2024) `a(n)` is the minimal permanent of an `n × n` symmetric
   Toeplitz matrix with `0` on the main diagonal and all the integers `1, 2, …, n-1` off the
   diagonal. Such a matrix is `T[i,j] = t(|i-j|)` with `t(0) = 0` and `t(1), …, t(n-1)` a
   permutation of `1, …, n-1`. The choice `t(k) = k` gives `a(n)`, so the claim is that every
   such permanent is `≥ a(n)`. Here `t(k) = σ(k-1) + 1` for a permutation `σ` of `Fin (n-1)`.
   Stated for `n ≥ 1` (checked by brute force for `n ≤ 8`).
-/

namespace OMA.S_oeis_a085807

/-- A085807. -/
def a (n : ℕ) : ℤ := Matrix.permanent (Matrix.of fun i j : Fin n => |(i : ℤ) - j|)

/-- The symmetric Toeplitz matrix with first row `0, σ(0)+1, …, σ(n-2)+1`. -/
def toeplitz (n : ℕ) (σ : Equiv.Perm (Fin (n - 1))) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j =>
    if h : i = j then 0
    else ((σ ⟨Int.natAbs ((i : ℤ) - j) - 1, by
      have hi := i.isLt; have hj := j.isLt
      have : (i : ℕ) ≠ j := fun e => h (Fin.ext e)
      omega⟩ : ℕ) : ℤ) + 1

theorem main :
    (∀ p : ℕ, p.Prime → p ≠ 2 → 2 * a p ≡ -1 [ZMOD p]) ∧
    (∀ n : ℕ, 1 ≤ n → ∀ σ : Equiv.Perm (Fin (n - 1)), a n ≤ Matrix.permanent (toeplitz n σ)) := by
  sorry

end OMA.S_oeis_a085807
