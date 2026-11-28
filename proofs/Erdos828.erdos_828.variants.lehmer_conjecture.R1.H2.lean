import OMAReductions.R_Erdos828_erdos_828_variants_lehmer_conjecture_R1

-- Step Erdos828.erdos_828.variants.lehmer_conjecture.R1.H2: hypothesis H2 of reduction Erdos828.erdos_828.variants.lehmer_conjecture.R1
-- Credit: @Solfanbtc

/-! The easy direction of Lehmer's totient problem: for a prime `n`, `φ n = n - 1`. -/

theorem OMA.solution : OMA.R_Erdos828_erdos_828_variants_lehmer_conjecture_R1.H2 := by
  intro n _ h
  simp [Nat.totient_prime (Nat.prime_iff.mpr h)]
