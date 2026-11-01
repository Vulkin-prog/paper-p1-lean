module

public import PaperP1.Asymptotics.LatePeelingOrder
public import PaperP1.Affine.PrivateRankCore

/-! # Controlling the actual denominator after private-rank peeling -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LatePeelingDensity

open Finset Filter PaperP1.Arithmetic PaperP1.LatePrimePopulation
  PaperP1.LatePrimeRankDensity PaperP1.LatePeelingOrder

local instance latePeelingDensityTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

theorem finite_density_bound {R E m t : ℝ} (hR : 0 ≤ R) (hRE : R ≤ E)
    (hm : 0 < m) (ht : 0 < t) (hEt : E / m < t) :
    0 < m - R / t ∧ R / (m - R / t) ≤ (E / m) / (1 - (E / m) / t) := by
  have hE : 0 ≤ E := hR.trans hRE
  have hEt' : E / t < m := by
    apply (div_lt_iff₀ ht).mpr
    have h := (div_lt_iff₀ hm).mp hEt
    nlinarith
  have hdenE : 0 < m - E / t := by linarith
  have hratio : R / t ≤ E / t := div_le_div_of_nonneg_right hRE ht.le
  have hdenR : 0 < m - R / t := by linarith
  have hsmall : (E / m) / t < 1 := (div_lt_iff₀ ht).mpr (by simpa only [one_mul] using hEt)
  have hsmallpos : 0 < 1 - (E / m) / t := by linarith
  have hid : E / (m - E / t) = (E / m) / (1 - (E / m) / t) := by
    apply (div_eq_div_iff hdenE.ne' hsmallpos.ne').mpr
    field_simp
  refine ⟨hdenR, ?_⟩
  calc
    _ ≤ E / (m - R / t) := div_le_div_of_nonneg_right hRE hdenR.le
    _ ≤ E / (m - E / t) := div_le_div_of_nonneg_left hE hdenE (by linarith)
    _ = _ := hid

def densityEnvelope (q : ℕ) : ℝ :=
  envelopeDensity q / (1 - envelopeDensity q / (order q : ℝ))

theorem order_real_tendsto : Tendsto (fun q : ℕ ↦ (order q : ℝ)) atTop atTop :=
  (tendsto_natCast_atTop_atTop (R := ℝ)).comp order_tendsto

theorem relative_loss_tendsto :
    Tendsto (fun q : ℕ ↦ envelopeDensity q / (order q : ℝ)) atTop (nhds 0) :=
  envelopeDensity_tendsto.div_atTop order_real_tendsto

theorem densityEnvelope_tendsto : Tendsto densityEnvelope atTop (nhds densityBound) := by
  unfold densityEnvelope
  have hden : Tendsto (fun q : ℕ ↦ 1 - envelopeDensity q / (order q : ℝ)) atTop (nhds 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub relative_loss_tendsto
  have h := envelopeDensity_tendsto.div hden (by norm_num : (1 : ℝ) ≠ 0)
  convert h using 1
  rw [div_one]

theorem actual_density_envelope :
    ∀ᶠ q : ℕ in atTop,
      0 < ((population q).card : ℝ) - (totalRank q : ℝ) / (order q : ℝ) ∧
        PrivateRankCore.density (spaces q) (population q) (order q) ≤ densityEnvelope q := by
  have hsmall := relative_loss_tendsto.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [eventually_ge_atTop 2, population_nonempty_eventually,
    order_positive_eventually, hsmall] with q hq hpop hord hsmallq
  have hm : (0 : ℝ) < (population q).card := by exact_mod_cast card_pos.mpr hpop
  have ht : (0 : ℝ) < order q := by exact_mod_cast (show 0 < order q by omega)
  have hEt : envelopeDensity q < (order q : ℝ) := by
    simpa only [one_mul] using (div_lt_iff₀ ht).mp hsmallq
  have hcalc := finite_density_bound (Nat.cast_nonneg (totalRank q)) (rank_le_envelope hq) hm ht hEt
  refine ⟨hcalc.1, ?_⟩
  simpa only [PrivateRankCore.density, totalRank, densityEnvelope, envelopeDensity] using hcalc.2

theorem actual_density_bound (η : ℝ) (hη : 0 < η) :
    ∀ᶠ q : ℕ in atTop,
      0 < ((population q).card : ℝ) - (totalRank q : ℝ) / (order q : ℝ) ∧
        PrivateRankCore.density (spaces q) (population q) (order q) ≤ densityBound + η := by
  have hlarge := densityEnvelope_tendsto.eventually
    (eventually_lt_nhds (by linarith : densityBound < densityBound + η))
  filter_upwards [actual_density_envelope, hlarge] with q hq hlargeq
  exact ⟨hq.1, hq.2.trans hlargeq.le⟩

end PaperP1.LatePeelingDensity
