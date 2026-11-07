module

public import PaperP1.Asymptotics.SharpPrimitiveNominalMass
public import PaperP1.Asymptotics.HomogeneousLocalMarginalCap

/-! # One homogeneous envelope for every fixed primitive arity

The exact homogeneous event probability is at most 2^r times the nominal
rank weight on the critical band. The already proved nominal estimates
therefore control homogeneous probabilities, original rank weights, actual
joint probabilities and absolute centered activities with the same exponents.
The arity is fixed before the scale threshold; no growing-order assertion is
made. No regularity, affine compatibility or positive original marginal is
assumed.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedArityHomogeneousMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.ConnectedWindowFamilies

theorem point_le_nominal (L : ℕ) (I : Finset ℕ)
    (hcap : ∀ x ∈ I, HomogeneousRunMass.probability L {x} ≤ 2 * (2 ^ L : ℝ)⁻¹) :
    HomogeneousRunMass.probability L I ≤
      (2 : ℝ) ^ I.card * PrimitiveNominalMass.weight L I := by
  rw [HomogeneousEffectiveWeights.factor, PrimitiveNominalMass.weight]
  have hprod : (∏ x ∈ I, HomogeneousRunMass.probability L {x}) ≤
      (2 * (2 ^ L : ℝ)⁻¹) ^ I.card := by
    calc
      _ ≤ ∏ _x ∈ I, 2 * (2 ^ L : ℝ)⁻¹ :=
        prod_le_prod₀ (fun x _ ↦ (HomogeneousRunMass.probability_pos L {x}).le) hcap
      _ = _ := prod_const _
  calc
    _ ≤ (2 * (2 ^ L : ℝ)⁻¹) ^ I.card *
        (2 ^ relativeNullityOn (fun x ↦ squareClassSpace x L) I : ℝ) :=
      mul_le_mul_of_nonneg_right hprod (by positivity)
    _ = _ := by rw [mul_pow]; ring

theorem mass_le_nominal (L r : ℕ) (F : Finset (Finset ℕ))
    (hcard : ∀ I ∈ F, I.card = r)
    (hcap : ∀ I ∈ F, ∀ x ∈ I,
      HomogeneousRunMass.probability L {x} ≤ 2 * (2 ^ L : ℝ)⁻¹) :
    (∑ I ∈ F, HomogeneousRunMass.probability L I) ≤
      (2 : ℝ) ^ r * PrimitiveNominalMass.mass F L := by
  calc
    _ ≤ ∑ I ∈ F, (2 : ℝ) ^ r * PrimitiveNominalMass.weight L I := by
      apply sum_le_sum
      intro I hI
      simpa only [hcard I hI] using point_le_nominal L I (hcap I hI)
    _ = _ := by rw [PrimitiveNominalMass.mass, mul_sum]

theorem uniform_nominal_cap (C : ℝ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      0 < L ∧ ∀ x ∈ dyadicBlock N,
        HomogeneousRunMass.probability L {x} ≤ 2 * (2 ^ L : ℝ)⁻¹ := by
  obtain ⟨NR, hr⟩ := LocalRigidityRegimes.critical_band_relation_rank_le_one (1 / 2) C (by norm_num)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max 2 (max NR NG), by omega, ?_⟩
  intro N hN L hband
  have hgeom := hg N (by omega) L hband
  have hL : 0 < L := by omega
  refine ⟨hL, ?_⟩
  intro x hx
  have hxpos : 0 < x := by have hh := (mem_Ico.mp hx).1; omega
  have hbase : (1 / 2 : ℝ) * N ≤ ((x - 1 : ℕ) : ℝ) := by
    have hh : N ≤ 2 * (x - 1) := by have h := (mem_Ico.mp hx).1; omega
    have hR : (N : ℝ) ≤ 2 * (x - 1 : ℕ) := by exact_mod_cast hh
    linarith only [hR]
  have hrel := hr N (by omega) (x - 1) L hbase hband
  rw [HomogeneousEffectiveWeights.singleton_rank]
  rcases LocalRigidityConsequences.effective_rank_eq_or_pred hxpos hrel with h | h
  · rw [h]
    have hp : 0 ≤ (2 ^ L : ℝ)⁻¹ := by positivity
    linarith only [hp]
  · rw [h, LocalRigidityConsequences.inverse_two_pow_pred hL]

theorem finite_original_domination (L : ℕ) (hL : 0 < L) (F : Finset (Finset ℕ))
    (hne : ∀ I ∈ F, I.Nonempty) :
    (∑ I ∈ F, PrimitiveWindowMass.weight L I) ≤
        (∑ I ∈ F, HomogeneousRunMass.probability L I) ∧
    (∑ I ∈ F, infiniteJointMoment L I) ≤
        (∑ I ∈ F, HomogeneousRunMass.probability L I) ∧
    (∑ I ∈ F, |infiniteCenteredCoefficient L I|) ≤
        (∑ I ∈ F, HomogeneousRunMass.probability L I) := by
  exact ⟨sum_le_sum fun I _ ↦ HomogeneousEffectiveWeights.weight_le L hL I,
    sum_le_sum fun I _ ↦ HomogeneousRunMass.actual_joint_le L hL I,
    sum_le_sum fun I hI ↦ HomogeneousEffectiveWeights.centered_le L hL I (hne I hI)⟩

theorem uniform_mass (r : ℕ) (hr : 3 ≤ r) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ I.card = r ∧ Primitive L I) →
        (∑ I ∈ F, HomogeneousRunMass.probability L I) ≤
          (N : ℝ) ^ (-(r : ℝ) / 2 + ε) := by
  obtain ⟨NM, _hNM, hm⟩ := SharpPrimitiveNominalMass.uniform_mass r hr C (ε / 2) (by positivity)
  obtain ⟨NC, _hNC, hc⟩ := uniform_nominal_cap C
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption ((2 : ℝ) ^ r)
    (-(r : ℝ) / 2 + ε / 2) (ε / 2) (by positivity)
  refine ⟨3 + NM + NC + NA, by omega, ?_⟩
  intro N hN L hband F hF
  have hcap := (hc N (by omega) L hband).2
  calc
    _ ≤ (2 : ℝ) ^ r * PrimitiveNominalMass.mass F L := mass_le_nominal L r F
      (fun I hI ↦ (hF I hI).2.1) (fun I hI x hx ↦ hcap x ((hF I hI).1 hx))
    _ ≤ (2 : ℝ) ^ r * (N : ℝ) ^ (-(r : ℝ) / 2 + ε / 2) :=
      mul_le_mul_of_nonneg_left (hm N (by omega) L hband F hF) (by positivity)
    _ ≤ (N : ℝ) ^ ((-(r : ℝ) / 2 + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

theorem uniform_dense_mass (r : ℕ) (hr : 3 ≤ r) (C η ε : ℝ)
    (hη : 0 < η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ I.card = r ∧ Primitive L I ∧
        η * L ≤ (runRelativeNullity L I : ℝ)) →
        (∑ I ∈ F, HomogeneousRunMass.probability L I) ≤
          (N : ℝ) ^ (1 - (r : ℝ) + ε) := by
  obtain ⟨NM, _hNM, hm⟩ := DensePrimitiveNominalMass.uniform_mass r hr C η (ε / 2) hη (by positivity)
  obtain ⟨NC, _hNC, hc⟩ := uniform_nominal_cap C
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption ((2 : ℝ) ^ r)
    (1 - (r : ℝ) + ε / 2) (ε / 2) (by positivity)
  refine ⟨3 + NM + NC + NA, by omega, ?_⟩
  intro N hN L hband F hF
  have hcap := (hc N (by omega) L hband).2
  calc
    _ ≤ (2 : ℝ) ^ r * PrimitiveNominalMass.mass F L := mass_le_nominal L r F
      (fun I hI ↦ (hF I hI).2.1) (fun I hI x hx ↦ hcap x ((hF I hI).1 hx))
    _ ≤ (2 : ℝ) ^ r * (N : ℝ) ^ (1 - (r : ℝ) + ε / 2) :=
      mul_le_mul_of_nonneg_left (hm N (by omega) L hband F (by
        intro I hI
        obtain ⟨hI, hcard, hprim, hdense⟩ := hF I hI
        exact ⟨hcard, hI, hprim, hdense⟩)) (by positivity)
    _ ≤ (N : ℝ) ^ ((1 - (r : ℝ) + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

/-- One scale threshold controls all four genuine weights and the dense host count. -/
theorem uniform_all_bounds (r : ℕ) (hr : 3 ≤ r) (C η ε : ℝ)
    (hη : 0 < η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (∀ F : Finset (Finset ℕ),
        (∀ I ∈ F, I ⊆ dyadicBlock N ∧ I.card = r ∧ Primitive L I) →
        (∑ I ∈ F, HomogeneousRunMass.probability L I) ≤ (N : ℝ) ^ (-(r : ℝ) / 2 + ε) ∧
        (∑ I ∈ F, PrimitiveWindowMass.weight L I) ≤ (N : ℝ) ^ (-(r : ℝ) / 2 + ε) ∧
        (∑ I ∈ F, infiniteJointMoment L I) ≤ (N : ℝ) ^ (-(r : ℝ) / 2 + ε) ∧
        (∑ I ∈ F, |infiniteCenteredCoefficient L I|) ≤ (N : ℝ) ^ (-(r : ℝ) / 2 + ε)) ∧
      (∀ F : Finset (Finset ℕ),
        (∀ I ∈ F, I ⊆ dyadicBlock N ∧ I.card = r ∧ Primitive L I ∧
          η * L ≤ (runRelativeNullity L I : ℝ)) →
        (F.card : ℝ) ≤ (N : ℝ) ^ ε ∧
        (∑ I ∈ F, HomogeneousRunMass.probability L I) ≤ (N : ℝ) ^ (1 - (r : ℝ) + ε) ∧
        (∑ I ∈ F, PrimitiveWindowMass.weight L I) ≤ (N : ℝ) ^ (1 - (r : ℝ) + ε) ∧
        (∑ I ∈ F, infiniteJointMoment L I) ≤ (N : ℝ) ^ (1 - (r : ℝ) + ε) ∧
        (∑ I ∈ F, |infiniteCenteredCoefficient L I|) ≤ (N : ℝ) ^ (1 - (r : ℝ) + ε)) := by
  obtain ⟨NM, _hNM, hm⟩ := uniform_mass r hr C ε hε
  obtain ⟨ND, _hND, hd⟩ := uniform_dense_mass r hr C η ε hη hε
  obtain ⟨NH, _hNH, hh⟩ := DensePrimitiveHosts.uniform_hosts r hr C η ε hη hε
  obtain ⟨NC, _hNC, hc⟩ := uniform_nominal_cap C
  refine ⟨3 + NM + ND + NH + NC, by omega, ?_⟩
  intro N hN L hband
  have hL := (hc N (by omega) L hband).1
  constructor
  · intro F hF
    have hb := hm N (by omega) L hband F hF
    obtain ⟨hw, hj, hz⟩ := finite_original_domination L hL F (by
      intro I hI
      exact card_pos.mp (by rw [(hF I hI).2.1]; omega))
    exact ⟨hb, hw.trans hb, hj.trans hb, hz.trans hb⟩
  · intro F hF
    have hb := hd N (by omega) L hband F hF
    have hn := hh N (by omega) L hband F (by
      intro I hI
      obtain ⟨hI, hcard, hprim, hdense⟩ := hF I hI
      exact ⟨hcard, hI, hprim, hdense⟩)
    obtain ⟨hw, hj, hz⟩ := finite_original_domination L hL F (by
      intro I hI
      exact card_pos.mp (by rw [(hF I hI).2.1]; omega))
    exact ⟨hn, hb, hw.trans hb, hj.trans hb, hz.trans hb⟩

end PaperP1.FixedArityHomogeneousMass
