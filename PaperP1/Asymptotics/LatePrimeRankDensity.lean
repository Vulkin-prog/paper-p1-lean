module

public import PaperP1.Asymptotics.LatePrimePopulation
public import PaperP1.Asymptotics.LateWindowRank

/-! # The literal late population and its bounded actual character-rank density -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LatePrimeRankDensity

open Finset Filter PaperP1.Arithmetic PaperP1.Model PaperP1.Affine
  PaperP1.SubspaceFamilyRank PaperP1.PrimeCylinderScale PaperP1.LatePrimePopulation

local instance latePrimeDensityTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

def cutoff (q : ℕ) : ℕ := 2 * size q + q

def spaces (q x : ℕ) : Submodule F₂ (SampleSpace (cutoff q) →ₗ[F₂] F₂) :=
  effectiveRowSpace (startSystem (cutoff q) x (q - 1))

def totalRank (q : ℕ) : ℕ := rank (spaces q) (population q)

def densityBound : ℝ := 17 / (6 * Real.log 2)

def envelopeDensity (q : ℕ) : ℝ := LatePrimeBudget.envelope (size q) / (population q).card

theorem densityBound_pos : 0 < densityBound := by
  unfold densityBound
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  positivity

theorem local_cutoff {q x : ℕ} (hx : x ∈ population q) : x + (q - 1) ≤ cutoff q := by
  have hxreg := RegularStarts.mem_regularStarts.mp (population_regular q hx)
  have hxb := mem_Ico.mp hxreg.1
  unfold cutoff
  omega

theorem local_rank {q x : ℕ} (hx : x ∈ population q) :
    Module.finrank F₂ (spaces q x) = q - 1 := by
  change Module.finrank F₂ (effectiveRowSpace (startSystem (cutoff q) x (q - 1))) = _
  rw [← finrank_squareClassSpace_eq_effectiveRows (local_cutoff hx)]
  exact (RegularStarts.mem_regularStarts.mp (population_regular q hx)).2

theorem common_equations {q : ℕ} (hq : Nat.Prime q) {x : ℕ} (hx : x ∈ population q) :
    startSystem (cutoff q) x (q - 1) (LatePrimeWindows.sample (size q) q hq) = startRhs (q - 1) := by
  apply (startSystem_eq_startRhs_iff _ (by have h := hq.two_le; omega)).mpr
  exact LatePrimeWindows.common_start_event hq (population_subset q hx)

theorem rank_le_envelope {q : ℕ} (hq : 2 ≤ q) :
    (totalRank q : ℝ) ≤ LatePrimeBudget.envelope (size q) := by
  have hfinite := LateWindowRank.finite_rank_le_cover (M := cutoff q) hq (population_subset q)
  have hfiniteR : (totalRank q : ℝ) ≤ (LateWindowPrimes.cover (size q)).card := by exact_mod_cast hfinite
  exact hfiniteR.trans (LatePrimeBudget.cover_card_le _)

theorem envelopeDensity_tendsto : Tendsto envelopeDensity atTop (nhds densityBound) := by
  have hlog2 : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hnum := LatePrimeBudget.envelope_ratio_tendsto.comp size_tendsto
  have hden := population_ratio.mul log_size_div_index_tendsto
  have hlim := hnum.div hden (mul_ne_zero (by norm_num : (1 / 2 : ℝ) ≠ 0) hlog2)
  have heq : envelopeDensity =ᶠ[atTop]
      (fun q : ℕ ↦ (LatePrimeBudget.envelope (size q) * Real.log (size q) / size q) /
        ((((population q).card : ℝ) * q / size q) * (Real.log (size q) / q))) := by
    filter_upwards [eventually_ge_atTop 2, population_nonempty_eventually] with q hq hpop
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    have hn : (size q : ℝ) ≠ 0 := by exact_mod_cast (size_pos q).ne'
    have hN2 : 1 < size q := by have h := index_le_size (by omega : 1 ≤ q); omega
    have hlog : Real.log (size q) ≠ 0 := (Real.log_pos (by exact_mod_cast hN2)).ne'
    have hm : ((population q).card : ℝ) ≠ 0 := by exact_mod_cast (card_pos.mpr hpop).ne'
    unfold envelopeDensity
    field_simp
  apply Tendsto.congr' heq.symm
  convert hlim using 1
  · rfl
  · unfold densityBound
    congr 1
    field_simp
    norm_num

theorem rank_ratio_bound (η : ℝ) (hη : 0 < η) :
    ∀ᶠ q : ℕ in atTop, (population q).Nonempty ∧
      (totalRank q : ℝ) / (population q).card ≤ densityBound + η := by
  have hlim := envelopeDensity_tendsto.eventually
    (eventually_lt_nhds (by linarith : densityBound < densityBound + η))
  filter_upwards [eventually_ge_atTop 2, population_nonempty_eventually, hlim] with q hq hpop hbound
  refine ⟨hpop, ?_⟩
  exact (div_le_div_of_nonneg_right (rank_le_envelope hq) (Nat.cast_nonneg _)).trans hbound.le

end PaperP1.LatePrimeRankDensity
