module

public import PaperP1.Asymptotics.RawPairResidualUnderInputs
public import PaperP1.Asymptotics.HomogeneousChannelMass
public import PaperP1.Model.HomogeneousSourcePairMass

/-! # The outside-principal homogeneous dependent-pair bound in companion T1.12(1) -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousPairResidualUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.HomogeneousRunMass
  PaperP1.PrincipalPositiveCover

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def families (N H L : ℕ) (G : Finset ℕ) : Finset (Finset ℕ) :=
  ((G.powersetCard 2 \ ClosePairs.pairs G L) \ HomogeneousChannelMass.rawPrincipal N H L).filter
    fun e ↦ 0 < runRelativeNullity L e

theorem mem_families (N H L : ℕ) (G e : Finset ℕ) :
    e ∈ families N H L G ↔ e ∈ G.powersetCard 2 ∧ e ∉ ClosePairs.pairs G L ∧
      e ∉ HomogeneousChannelMass.rawPrincipal N H L ∧ 0 < runRelativeNullity L e := by
  simp only [families, mem_filter, mem_sdiff, and_assoc]

theorem subset_off_principal {N H L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) :
    families N H L G ⊆ separated N L \ principal N H L := by
  intro e he
  obtain ⟨heG, hclose, hprincipal, _hdep⟩ := (mem_families N H L G e).mp he
  obtain ⟨hesub, hecard⟩ := mem_powersetCard.mp heG
  have heN : e ∈ (dyadicBlock N).powersetCard 2 := mem_powersetCard.mpr ⟨hesub.trans hG, hecard⟩
  have hnotclose : e ∉ ClosePairs.pairs (dyadicBlock N) L := by
    intro hc
    exact hclose (mem_filter.mpr ⟨heG, (mem_filter.mp hc).2⟩)
  change e ∉ principal N H L at hprincipal
  exact mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨heN, hnotclose⟩, hprincipal⟩

theorem homogeneous_mass_eq {N H L : ℕ} {G : Finset ℕ} (hG : G ⊆ RegularStarts.regularStarts N L) :
    (∑ e ∈ families N H L G, probability L e) = PrimitiveNominalMass.mass (families N H L G) L := by
  apply sum_congr rfl
  intro e he
  exact regular_weight (((mem_powersetCard.mp ((mem_families N H L G e).mp he).1).1).trans hG)

theorem finite_mass_bound {N H L : ℕ} {G : Finset ℕ} (hG : G ⊆ RegularStarts.regularStarts N L) :
    PrimitiveNominalMass.mass (families N H L G) L ≤
      2 * ((2 ^ L : ℝ)⁻¹) ^ 2 *
        (∑ e ∈ separated N L \ principal N H L, SourcePairPositiveWeight.setWeight L e) := by
  have hsub := subset_off_principal (H := H) (L := L) (hG.trans (RegularStarts.regularStarts_subset N L))
  calc
    _ ≤ ∑ e ∈ families N H L G, 2 * ((2 ^ L : ℝ)⁻¹) ^ 2 * SourcePairPositiveWeight.setWeight L e := by
      apply sum_le_sum
      intro e he
      obtain ⟨heG, _hclose, _hprincipal, hdep⟩ := (mem_families N H L G e).mp he
      obtain ⟨hesub, hecard⟩ := mem_powersetCard.mp heG
      exact HomogeneousSourcePairMass.regular_dependent_bound
        (mem_powersetCard.mpr ⟨hesub.trans hG, hecard⟩) hdep
    _ = 2 * ((2 ^ L : ℝ)⁻¹) ^ 2 *
        (∑ e ∈ families N H L G, SourcePairPositiveWeight.setWeight L e) := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_le_sum_of_subset_of_nonneg hsub (fun e _ _ ↦ SourcePairPositiveWeight.setWeight_nonneg L e)) (by positivity)

theorem companion_T1_12_pair_residual (C ε : ℝ) (D : ℕ) (hε : 0 < ε) :
    ∃ Ds k k₁ k₂ : ℕ, 0 < Ds ∧
      (UniformSourceSurfaceCover.UniformCover k (GeneralGraphHostCount.sizeCap (ε / 384)) Ds →
      UniformOrdinarySurfaceCover.UniformCover k₁ 2 →
      UniformOrdinarySurfaceCover.UniformCover k₂ 3 →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((Ds + 2).choose 2 + k) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k₁ + 3) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k₂ + 3) M) →
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        8 * (L + 1) ≤ H → H ≤ D * (L + 1) →
        ∀ G : Finset ℕ, G ⊆ RegularStarts.regularStarts N L →
        (PrimitiveNominalMass.mass (families N H L G) L ≤ (N : ℝ) ^ (-4 / 5 + ε) ∧
          (∑ e ∈ families N H L G, probability L e) ≤ (N : ℝ) ^ (-4 / 5 + ε))) := by
  obtain ⟨Ds, k, k₁, k₂, hDs, hraw⟩ := RawPairResidualUnderInputs.uniform_bound C (ε / 3) D (by positivity)
  rw [show (ε / 3) / 128 = ε / 384 by ring] at hraw
  let K : ℝ := ((2 : ℝ) ^ C) ^ 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (2 * K) (-4 / 5 + ε / 3) (2 * ε / 3) (by positivity)
  refine ⟨Ds, k, k₁, k₂, hDs, ?_⟩
  intro hCover hCover₁ hCover₂ hPila hPila₁ hPila₂
  obtain ⟨NR, _hNR, hr⟩ := hraw hCover hCover₁ hCover₂ hPila hPila₁ hPila₂
  refine ⟨max 2 (max NR NF), by omega, ?_⟩
  intro N hN L H hband hcut hH G hG
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hrawmass := hr N (by omega) L H hband hcut hH
  have hnominal := CriticalChannelPowers.nominal_square_upper (by omega : 2 ≤ N) hband
  have hmass : PrimitiveNominalMass.mass (families N H L G) L ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
    calc
      _ ≤ 2 * ((2 ^ L : ℝ)⁻¹) ^ 2 *
          (∑ e ∈ separated N L \ principal N H L, SourcePairPositiveWeight.setWeight L e) := finite_mass_bound hG
      _ ≤ (2 * (K * (N : ℝ) ^ (-2 : ℝ))) * (N : ℝ) ^ (6 / 5 + ε / 3) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hnominal (by norm_num)) hrawmass
          (sum_nonneg fun e _ ↦ SourcePairPositiveWeight.setWeight_nonneg L e) (by positivity)
      _ = (2 * K) * (N : ℝ) ^ (-4 / 5 + ε / 3) := by
        rw [show (-4 / 5 : ℝ) + ε / 3 = -2 + (6 / 5 + ε / 3) by ring,
          Real.rpow_add hn (-2) (6 / 5 + ε / 3)]
        ring
      _ ≤ (N : ℝ) ^ ((-4 / 5 + ε / 3) + 2 * ε / 3) := hf N (by omega)
      _ = _ := by congr 1; ring
  exact ⟨hmass, by rw [homogeneous_mass_eq hG]; exact hmass⟩

end PaperP1.HomogeneousPairResidualUnderInputs
