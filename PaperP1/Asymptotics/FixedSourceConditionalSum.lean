module

public import PaperP1.Model.WindowConditionalSum
public import PaperP1.Model.CompatibleWindowPrescriptions
public import PaperP1.Asymptotics.SmallRankLossPower
public import PaperP1.Asymptotics.DenseTargetCount

/-! # The full conditional-sum assertion of main Proposition 6.3 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedSourceConditionalSum

open Finset Filter PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.WindowFamilyConditional
  PaperP1.Model.InfiniteRademacher PaperP1.CriticalBandScale

local instance fixedSourceConditionalSumTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance fixedSourceConditionalSumMeasurableF2 : MeasurableSpace F₂ := ⊤

theorem witness_sum (s : ℕ) (hs : 1 ≤ s) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ x : Fin s → ℕ, (∀ i, x i ∈ Ico N (2 * N)) →
      ∀ M : ℕ, 2 * N + L ≤ M → ∀ a : SampleSpace M, ∀ c : ℕ → Fin L → F₂,
        (∑ z ∈ Ico N (2 * N), conditionalProbability x L (fun i ↦ startSystem M (x i) L a) z (c z)) ≤
          (N : ℝ) ^ ε := by
  let η := ε / (4 * upperScale * Real.log 2)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hupper := upperScale_pos
  have hη : 0 < η := by dsimp [η]; exact div_pos hε (by positivity)
  have hηpower : η * upperScale * Real.log 2 = ε / 4 := by
    dsimp [η]
    field_simp
  obtain ⟨ND, hND⟩ := DenseTargetCount.uniform_count s hs C η (ε / 4) hη (by positivity)
  obtain ⟨NR, hNR⟩ := LocalRigidityRegimes.critical_band_relation_rank_le_one (1 / 2) C (by norm_num)
  obtain ⟨NG, hNG⟩ := critical_band_scale C
  let K : ℝ := 2 * (2 : ℝ) ^ C
  have hlarge : ∀ᶠ N : ℕ in atTop, K + 1 ≤ (N : ℝ) ^ (ε / 2) :=
    ((tendsto_rpow_atTop (by positivity : 0 < ε / 2)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (eventually_ge_atTop (K + 1))
  obtain ⟨NA, hNA⟩ := eventually_atTop.1 hlarge
  refine ⟨max ND (max NR (max NG (max NA 2))), ?_⟩
  intro N hN L hband x hx M hM a c
  have hN2 : 2 ≤ N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hcut : ∀ i, x i + L ≤ M := by
    intro i
    have h := (mem_Ico.mp (hx i)).2
    omega
  have hrel : ∀ z ∈ Ico N (2 * N),
      Module.finrank F₂ (WindowRelationCode.windowRelationCode (z - 1) (L + 1)) ≤ 1 := by
    intro z hz
    have hzN := (mem_Ico.mp hz).1
    have hnat : N ≤ 2 * (z - 1) := by omega
    have hreal : (N : ℝ) ≤ 2 * ((z - 1 : ℕ) : ℝ) := by exact_mod_cast hnat
    exact hNR N (by omega) (z - 1) L (by nlinarith only [hreal]) hband
  have hfinite := WindowConditionalSum.finite_bound x a c hcut hM hrel η
  have hlow := SmallRankLossPower.low_sum_bound hN2 hband (hNG N (by omega) L hband).2 η hη.le
  rw [hηpower] at hlow
  have hhigh := hND N (by omega) L hband x hx
  calc
    _ ≤ _ := hfinite
    _ ≤ (K + 1) * (N : ℝ) ^ (ε / 4) := by
      change _ ≤ (2 * (2 : ℝ) ^ C + 1) * (N : ℝ) ^ (ε / 4)
      nlinarith only [hlow, hhigh]
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 4) :=
      mul_le_mul_of_nonneg_right (hNA N (by omega)) (Real.rpow_nonneg hNr.le _)
    _ = (N : ℝ) ^ (3 * ε / 4) := by rw [← Real.rpow_add hNr]; congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [hε])

/-- Arbitrary compatible affine prescriptions at the sources and arbitrary
target prescriptions, even depending on the target centre. -/
theorem conditional_sum (s : ℕ) (hs : 1 ≤ s) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ x : Fin s → ℕ, (∀ i, x i ∈ Ico N (2 * N)) →
      ∀ b : Fin s → Fin L → F₂,
        0 < infiniteRademacherMeasure.real {ω | sourceEvent x L b ω} →
      ∀ c : ℕ → Fin L → F₂,
        (∑ z ∈ Ico N (2 * N), conditionalProbability x L b z (c z)) ≤ (N : ℝ) ^ ε := by
  obtain ⟨N₀, hN₀⟩ := witness_sum s hs C ε hε
  refine ⟨N₀, ?_⟩
  intro N hN L hband x hx b hb c
  let M := 2 * N + L
  have hcut : ∀ i, x i + L ≤ M := by
    intro i
    have h := (mem_Ico.mp (hx i)).2
    dsimp [M]
    omega
  obtain ⟨a, ha⟩ := CompatibleWindowPrescriptions.exists_witness_of_positive x b hcut hb
  have heq : b = fun i ↦ startSystem M (x i) L a := funext fun i ↦ (ha i).symm
  rw [heq]
  exact hN₀ N hN L hband x hx M le_rfl a c

theorem homogeneous_sum (s : ℕ) (hs : 1 ≤ s) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ x : Fin s → ℕ, (∀ i, x i ∈ Ico N (2 * N)) →
        (∑ z ∈ Ico N (2 * N), conditionalProbability x L (fun _ ↦ 0) z 0) ≤ (N : ℝ) ^ ε := by
  obtain ⟨N₀, hN₀⟩ := conditional_sum s hs C ε hε
  refine ⟨N₀, ?_⟩
  intro N hN L hband x hx
  apply hN₀ N hN L hband x hx (fun _ ↦ 0)
  apply CompatibleWindowPrescriptions.homogeneous_source_positive (M := 2 * N + L) x
  intro i
  have h := (mem_Ico.mp (hx i)).2
  omega

/-- The source-excluding sum stated in the first display of main 6.3. -/
theorem fresh_conditional_sum (s : ℕ) (hs : 1 ≤ s) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ x : Fin s → ℕ, (∀ i, x i ∈ Ico N (2 * N)) →
      ∀ b : Fin s → Fin L → F₂,
        0 < infiniteRademacherMeasure.real {ω | sourceEvent x L b ω} →
      ∀ c : ℕ → Fin L → F₂,
        (∑ z ∈ Ico N (2 * N) \ univ.image x, conditionalProbability x L b z (c z)) ≤ (N : ℝ) ^ ε := by
  obtain ⟨N₀, hN₀⟩ := conditional_sum s hs C ε hε
  refine ⟨N₀, ?_⟩
  intro N hN L hband x hx b hb c
  apply (sum_le_sum_of_subset_of_nonneg sdiff_subset (fun z _ _ ↦ conditionalProbability_nonneg x b (c z))).trans
  exact hN₀ N hN L hband x hx b hb c

end PaperP1.FixedSourceConditionalSum
