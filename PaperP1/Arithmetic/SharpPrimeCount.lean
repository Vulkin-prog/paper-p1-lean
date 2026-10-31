module

public import PaperP1.PNT.PrimeCountingAsymptotic
public import PaperP1.Coding.LocalRigidityCode

/-!
# The sharp prime-count input for local rigidity

The selected, recompiled Wiener--Ikehara proof of PNT supplies the ordinary
inclusive prime-count ratio and its one-sided consequence. The threshold is
chosen before every variable cutoff. No PNT proposition is a premise.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SharpPrimeCount

open Filter Real Asymptotics LocalDefectBound LocalRigidityCode

/-- The standard sequential PNT, with pi counting primes up to and including B. -/
theorem prime_counting_ratio_tendsto :
    Tendsto (fun B : ℕ ↦ (Nat.primeCounting B : ℝ) * Real.log B / B)
      atTop (nhds 1) := by
  obtain ⟨c, hc, heq⟩ := PNT.pi_alt
  have hc0 : Tendsto c atTop (nhds 0) := (isLittleO_one_iff ℝ).mp hc
  have hcN := hc0.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hratio : (fun B : ℕ ↦ (Nat.primeCounting B : ℝ) * Real.log B / B)
      =ᶠ[atTop] (fun B : ℕ ↦ 1 + c B) := by
    filter_upwards [eventually_ge_atTop 2] with B hB
    have hBpos : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
    have hlog : 0 < Real.log B := Real.log_pos (by exact_mod_cast (show 1 < B by omega))
    have h := heq (B : ℝ)
    simp only [Nat.floor_natCast] at h
    rw [h]
    field_simp [hBpos.ne', hlog.ne']
  have hlim : Tendsto (fun B : ℕ ↦ 1 + c B) atTop (nhds (1 + 0)) :=
    tendsto_const_nhds.add hcN
  exact Tendsto.congr' hratio.symm (by simpa only [add_zero] using hlim)

/-- Sharp leading constant, uniformly in every sufficiently large integer cutoff. -/
theorem primeCount_upper_eventually (η : ℝ) (hη : 0 < η) :
    ∃ B₀ : ℕ, 2 ≤ B₀ ∧ ∀ B : ℕ, B₀ ≤ B →
      (primeCount B : ℝ) ≤ (1 + η) * B / Real.log B := by
  obtain ⟨c, hc, heq⟩ := PNT.pi_alt
  have hc0 : Tendsto c atTop (nhds 0) := (isLittleO_one_iff ℝ).mp hc
  have hsmall : ∀ᶠ x : ℝ in atTop, c x < η :=
    hc0.eventually (eventually_lt_nhds hη)
  have hnat := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hsmall
  obtain ⟨B₁, hB₁⟩ := eventually_atTop.mp hnat
  refine ⟨max 2 B₁, le_max_left _ _, fun B hB ↦ ?_⟩
  have hBtwo : 2 ≤ B := (le_max_left _ _).trans hB
  have hsmallB := hB₁ B ((le_max_right _ _).trans hB)
  have hlog : 0 < Real.log B := Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  have h := heq (B : ℝ)
  simp only [Nat.floor_natCast] at h
  rw [primeCount_eq_primeCounting, h]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by linarith : 1 + c B ≤ 1 + η) (Nat.cast_nonneg B))
    hlog.le

end PaperP1.SharpPrimeCount
