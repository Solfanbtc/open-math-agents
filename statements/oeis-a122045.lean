import Mathlib

/-!
# A122045: Euler (or secant) numbers E(n).

Source: https://oeis.org/A122045
Credit: @Solfanbtc

The Euler numbers `E(n)` (offset 0) have e.g.f. `sech x = 1/cosh x`:
`1, 0, -1, 0, 5, 0, -61, 0, 1385, ...`.

The entry records that the odd primes `p` with `p ∣ E(p-1)` are the primes `p ≡ 1 (mod 4)`
(A002144), and conjectures: the odd composites `m` with `m ∣ E(m-1)` are the Carmichael numbers
`m` such that `p ≡ 1 (mod 4)` for every prime `p ∣ m` (A265237, starting `1105, ...`).
Stated as an equivalence for every odd composite `m`.

A python3 check (`|E(m-1)| mod m` via the Seidel–Entringer boustrophedon): for all odd
composites `m ≤ 1700` the two conditions agree (the only such `m` is `1105 = 5 · 13 · 17`).

Conventions:
* `E(n) = n! · [xⁿ] (cosh x)⁻¹`, computed in `ℚ⟦X⟧` with `cosh x = ∑_{n even} xⁿ/n!`. The
  values are integers; `m ∣ E(m-1)` is written `∃ z : ℤ, E(m-1) = m z`.
* Carmichael number (A002997): composite `m` with `b^{m-1} ≡ 1 (mod m)` for every `b` coprime to
  `m`. Composite: `1 < m` and `m` not prime.
-/

namespace OMA.S_oeis_a122045

open PowerSeries

/-- The series `cosh x`. -/
noncomputable def coshSeries : ℚ⟦X⟧ := mk fun n => if Even n then (1 : ℚ) / n.factorial else 0

/-- Euler numbers: `E(n) = n! [xⁿ] sech x`. -/
noncomputable def E (n : ℕ) : ℚ := (n.factorial : ℚ) * coeff n coshSeries⁻¹

/-- Carmichael numbers. -/
def IsCarmichael (m : ℕ) : Prop :=
  1 < m ∧ ¬ m.Prime ∧ ∀ b : ℕ, Nat.Coprime b m → b ^ (m - 1) ≡ 1 [MOD m]

/-- Conjecture: an odd composite `m` divides `E(m-1)` iff `m` is a Carmichael number all of whose
prime factors are `≡ 1 (mod 4)`. -/
theorem main : ∀ m : ℕ, Odd m → 1 < m → ¬ m.Prime →
    ((∃ z : ℤ, E (m - 1) = (m : ℚ) * z) ↔
      (IsCarmichael m ∧ ∀ p : ℕ, p.Prime → p ∣ m → p % 4 = 1)) := by
  sorry

end OMA.S_oeis_a122045
