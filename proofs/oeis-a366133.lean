import OMAStatements.S_oeis_a366133
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Prime.Basic

/-! OEIS A366133: `T(n, k) = C(n, k) * A005444(n - k)`, so it is enough that the binomial factor is
divisible. For a prime `p` and `0 < k < p`, `p ∣ C(p, k)`. For odd `k` with `0 < k < 2^m`,
`2^m * C(2^m - 1, k - 1) = C(2^m, k) * k` and `k` is prime to `2^m`, so `2^m ∣ C(2^m, k)`. -/

namespace OpenMath.A366133

open OMA.S_oeis_a366133

private theorem two_pow_dvd_choose (m k : ℕ) (hk : 0 < k) (hodd : Odd k) :
    2 ^ m ∣ Nat.choose (2 ^ m) k := by
  have h := Nat.add_one_mul_choose_eq (2 ^ m - 1) (k - 1)
  rw [Nat.sub_add_cancel Nat.one_le_two_pow, Nat.sub_add_cancel hk] at h
  have hcop : Nat.Coprime (2 ^ m) k := Nat.Coprime.pow_left m (Nat.coprime_two_left.2 hodd)
  exact hcop.dvd_of_dvd_mul_right (Dvd.intro _ h)

theorem main :
    (∀ p k : ℕ, p.Prime → 0 < k → k < p → (p : ℤ) ∣ a366133 p k) ∧
    (∀ m k : ℕ, 0 < k → k < 2 ^ m → Odd k → ((2 ^ m : ℕ) : ℤ) ∣ a366133 (2 ^ m) k) := by
  refine ⟨fun p k hp hk hkp => ?_, fun m k hk _ hodd => ?_⟩
  · unfold a366133
    exact (Int.natCast_dvd_natCast.2 (hp.dvd_choose_self hk.ne' hkp)).mul_right _
  · unfold a366133
    exact (Int.natCast_dvd_natCast.2 (two_pow_dvd_choose m k hk hodd)).mul_right _

end OpenMath.A366133

theorem OMA.solution : type_of% @OMA.S_oeis_a366133.main := OpenMath.A366133.main
