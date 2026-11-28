import Mathlib

/-!
# A133501: Number of steps for "powertrain" operation to converge when started at n.

Source: https://oeis.org/A133501
Credit: @Solfanbtc

The powertrain map (J. H. Conway, OEIS A133500): if `abcd...` is the decimal expansion of `n`,
then `powertrain(n) = a^b * c^d * ...`, ending in an exponent or a base according as the number
of digits is even or odd; `0^0 = 1`, and `powertrain(0) = 0` by convention.
A133501(n) is the number of steps the iteration started at `n` needs to reach a fixed point.

Conjecture (OEIS A133501, also stated in A287877): every number converges to a fixed point,
i.e. for every `n ≥ 0` some iterate `powertrain^[k] n` is a fixed point of `powertrain`.
(A135385 lists the known fixed points 0..9, 2592, 24547284284866560000000000; that the list is
complete is a separate conjecture, not stated here.)

Checked by `#eval`: `powertrain` reproduces the 65 listed terms of A133500, and the least `k`
with `powertrain^[k] n` a fixed point reproduces all 105 listed terms of A133501 (n = 0..104).
-/

namespace OMA.S_oeis_a133501

/-- `train [d₁, d₂, d₃, d₄, ...] = d₁ ^ d₂ * d₃ ^ d₄ * ...`, a trailing unpaired digit is a factor. -/
def train : List ℕ → ℕ
  | [] => 1
  | [x] => x
  | u :: v :: ws => u ^ v * train ws

/-- The powertrain map A133500 (decimal digits taken from the most significant one). -/
def powertrain (n : ℕ) : ℕ :=
  if n = 0 then 0 else train (Nat.digits 10 n).reverse

/-- Conjecture: every trajectory of the powertrain map reaches a fixed point. -/
theorem main : ∀ n : ℕ, ∃ k : ℕ, powertrain (powertrain^[k] n) = powertrain^[k] n := by
  sorry

end OMA.S_oeis_a133501
