module

public import PaperP1.Arithmetic.ParticipatingWindowCertificates
public import PaperP1.Asymptotics.LogPowerExponential
public import PaperP1.Asymptotics.LogarithmicWordPowers

/-! # Actual marked-window counts with a general polylogarithmic cutoff and a power kernel threshold -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MarkedWindowCount

open Finset Filter PaperP1.Arithmetic PaperP1.RankinSmallKernel

def marked (B N : ℕ) (Y T : ℝ) : Finset ℕ := by
  classical
  exact (Ico N (2 * N)).filter fun x ↦ ∃ u : Fin B, (truncatedKernel Y (x - 1 + u.val) : ℝ) ≤ T

theorem mem_marked (B N : ℕ) (Y T : ℝ) (x : ℕ) :
    x ∈ marked B N Y T ↔ x ∈ Ico N (2 * N) ∧ ¬ ModerateCertificateCount.Unmarked B Y T x := by
  classical
  simp only [marked, mem_filter, ModerateCertificateCount.Unmarked, not_forall, not_lt]

theorem finite_bound (B N : ℕ) (hN : 10 ≤ N) (hBN : B ≤ N + 1) (Y T : ℝ) :
    (marked B N Y T).card ≤ B * (RankinSmallKernel.values (3 * N) Y T).card := by
  classical
  let F := fun u : Fin B ↦ (Ico N (2 * N)).filter fun x ↦ (truncatedKernel Y (x - 1 + u.val) : ℝ) ≤ T
  have hcover : marked B N Y T ⊆ univ.biUnion F := by
    intro x hx
    obtain ⟨hx, u, hu⟩ := mem_filter.mp hx
    exact mem_biUnion.mpr ⟨u, mem_univ _, mem_filter.mpr ⟨hx, hu⟩⟩
  have hF (u : Fin B) : (F u).card ≤ (RankinSmallKernel.values (3 * N) Y T).card := by
    apply card_le_card_of_injOn (fun x ↦ x - 1 + u.val)
    · intro x hx
      obtain ⟨hx, hkernel⟩ := mem_filter.mp hx
      obtain ⟨hpos, hhi⟩ := SaturationPrimes.value_bounds hN hBN hx u
      exact (RankinSmallKernel.mem_values _ _ _ (by positivity) _).mpr
        ⟨hpos, by exact_mod_cast hhi, hkernel⟩
    · intro x hx y hy hxy
      have hxN := (mem_Ico.mp (mem_filter.mp hx).1).1
      have hyN := (mem_Ico.mp (mem_filter.mp hy).1).1
      change x - 1 + u.val = y - 1 + u.val at hxy
      omega
  calc
    _ ≤ (univ.biUnion F).card := card_le_card hcover
    _ ≤ ∑ u, (F u).card := card_biUnion_le
    _ ≤ ∑ _u : Fin B, (RankinSmallKernel.values (3 * N) Y T).card := sum_le_sum fun u _ ↦ hF u
    _ = _ := by simp

theorem logarithmic_exponential (K q ε : ℝ) (hq : q < 1) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, Real.exp (K * (Real.log N) ^ q) ≤ (N : ℝ) ^ ε := by
  have hlim := (LogPowerExponential.log_power_ratio_tendsto q hq).const_mul K
  filter_upwards [hlim.eventually (eventually_lt_nhds (by simpa only [mul_zero] using hε)),
    eventually_ge_atTop 2] with N hsmall hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  rw [← mul_div_assoc] at hsmall
  have hb := (div_lt_iff₀ hl).mp hsmall
  rw [Real.rpow_def_of_pos hn]
  apply Real.exp_le_exp.mpr
  linarith only [hb]

theorem uniform_count (A β σ D ε : ℝ) (hσ : 1 / 2 ≤ σ) (hσ1 : σ < 1)
    (hβ : 0 ≤ β) (hD : 0 ≤ D) (hgap : A * (1 - σ) < 1) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      L + 1 ≤ N + 1 → ((L + 1 : ℕ) : ℝ) ≤ D * Real.log N →
      ((marked (L + 1) N ((Real.log N) ^ A) ((N : ℝ) ^ β)).card : ℝ) ≤
        (N : ℝ) ^ (1 - (1 - β) * (1 - σ) + ε) := by
  obtain ⟨NE, he⟩ := eventually_atTop.mp (logarithmic_exponential (exponentConstant σ)
    (A * (1 - σ)) (ε / 2) hgap (by positivity))
  obtain ⟨NP, hp⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    D hD (countConstant σ 3) 1 (ε / 2) (by positivity)
  refine ⟨max 10 (max NE NP), by omega, ?_⟩
  intro N hN L hBN hwidth
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hn1
  have hfinite : ((marked (L + 1) N ((Real.log N) ^ A) ((N : ℝ) ^ β)).card : ℝ) ≤
      ((L + 1 : ℕ) : ℝ) * (RankinSmallKernel.values (3 * N) ((Real.log N) ^ A) ((N : ℝ) ^ β)).card := by
    exact_mod_cast finite_bound (L + 1) N (by omega) hBN ((Real.log N) ^ A) ((N : ℝ) ^ β)
  have hr := main_7_1_explicit σ hσ hσ1 3 (by norm_num) N ((Real.log N) ^ A) ((N : ℝ) ^ β)
    (Real.rpow_nonneg hlog _) (Real.one_le_rpow hn1 hβ)
  have hpoly : ((L + 1 : ℕ) : ℝ) * countConstant σ 3 ≤ (N : ℝ) ^ (ε / 2) := by
    have h := (le_abs_self _).trans (hp N (by omega) L hwidth)
    simpa only [pow_one, Nat.cast_add, Nat.cast_one, mul_comm] using h
  calc
    _ ≤ ((L + 1 : ℕ) : ℝ) * (countConstant σ 3 * (N : ℝ) ^ σ *
        ((N : ℝ) ^ β) ^ (1 - σ) * Real.exp (exponentConstant σ * ((Real.log N) ^ A) ^ (1 - σ))) :=
      hfinite.trans (mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg _))
    _ = (((L + 1 : ℕ) : ℝ) * countConstant σ 3) * (N : ℝ) ^ (σ + β * (1 - σ)) *
        Real.exp (exponentConstant σ * (Real.log N) ^ (A * (1 - σ))) := by
      rw [← Real.rpow_mul hn.le, ← Real.rpow_mul hlog, Real.rpow_add hn]
      ring
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (σ + β * (1 - σ)) * (N : ℝ) ^ (ε / 2) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hpoly (Real.rpow_nonneg hn.le _))
        (he N (by omega)) (Real.exp_nonneg _) (by positivity)
    _ = _ := by rw [← Real.rpow_add hn, ← Real.rpow_add hn]; congr 1; ring

end PaperP1.MarkedWindowCount
