module

public import PaperP1.Asymptotics.DensePrimitiveTripleHosts
public import PaperP1.Asymptotics.PrimitiveGeneralMass
public import PaperP1.Asymptotics.CriticalChannelPowers
public import PaperP1.Model.PrimitiveNominalMass

/-! # Dense primitive triples have heterogeneous and nominal rank mass of power two -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DensePrimitiveTripleRankMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.ConnectedWindowFamilies PaperP1.PrimitiveWindowMass PaperP1.FamilyIndependentMass

theorem uniform_rank_mass
    (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I.card = 3 ∧ I ⊆ dyadicBlock N ∧ Primitive L I ∧
        η * L ≤ (runRelativeNullity L I : ℝ)) → mass F L ≤ (N : ℝ) ^ (-2 + ε) := by
  obtain ⟨NH, _hNH, hh⟩ := DensePrimitiveTripleHosts.uniform_hosts
    C η (ε / 2) hη (by positivity)
  obtain ⟨K, hK, NM, hm⟩ := OriginalWindowFamilyMass.uniform_marginals C
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption ((2 : ℝ) ^ C * K ^ 3)
    (-2 + ε / 2) (ε / 2) (by positivity)
  refine ⟨3 + NH + NM + NA, by omega, ?_⟩
  intro N hN L hband F hF
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcount := hh N (by omega) L hband F hF
  have hcap := finite_mass_cap F (dyadicBlock N) L 3 (K / N)
    (fun I hI ↦ ⟨(hF I hI).2.1, (hF I hI).1⟩)
    (fun x hx ↦ (hm N (by omega) L x hband hx).2)
  have hdata : ∀ I ∈ F, I.Nonempty ∧ Primitive L I ∧ ∀ x ∈ I, 0 < x := by
    intro I hI
    refine ⟨card_pos.mp (by rw [(hF I hI).1]; omega), (hF I hI).2.2.1, ?_⟩
    intro x hx
    have hh := (mem_Ico.mp ((hF I hI).2.1 hx)).1
    omega
  have hproduct : ((2 : ℝ) ^ C * N) * ((N : ℝ) ^ (ε / 2) * (K / N) ^ 3) =
      ((2 : ℝ) ^ C * K ^ 3) * (N : ℝ) ^ (-2 + ε / 2) := by
    conv_rhs =>
      rw [show -2 + ε / 2 = (ε / 2 + 1) - 3 by ring,
        Real.rpow_sub hn, Real.rpow_add hn, Real.rpow_one, Real.rpow_ofNat]
    rw [div_pow]
    field_simp
  calc
    _ ≤ (2 ^ L : ℝ) * independentMass F L := primitive_mass_le F L hdata
    _ ≤ ((2 : ℝ) ^ C * N) * ((F.card : ℝ) * (K / N) ^ 3) :=
      mul_le_mul (PrimitiveGeneralMass.binary_factor (by omega) hband) hcap
        (sum_nonneg fun I _hI ↦ prod_nonneg fun x _hx ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)
        (by positivity)
    _ ≤ ((2 : ℝ) ^ C * N) * ((N : ℝ) ^ (ε / 2) * (K / N) ^ 3) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcount (by positivity)) (by positivity)
    _ = ((2 : ℝ) ^ C * K ^ 3) * (N : ℝ) ^ (-2 + ε / 2) := hproduct
    _ ≤ (N : ℝ) ^ ((-2 + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

theorem uniform_nominal_mass
    (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I.card = 3 ∧ I ⊆ dyadicBlock N ∧ Primitive L I ∧
        η * L ≤ (runRelativeNullity L I : ℝ)) →
      PrimitiveNominalMass.mass F L ≤ (N : ℝ) ^ (-2 + ε) := by
  obtain ⟨NH, _hNH, hh⟩ := DensePrimitiveTripleHosts.uniform_hosts
    C η (ε / 2) hη (by positivity)
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption (((2 : ℝ) ^ C) ^ 2)
    (-2 + ε / 2) (ε / 2) (by positivity)
  refine ⟨3 + NH + NA, by omega, ?_⟩
  intro N hN L hband F hF
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcount := hh N (by omega) L hband F hF
  have hdata : ∀ I ∈ F, I.card = 3 ∧ Primitive L I ∧ ∀ x ∈ I, 0 < x := by
    intro I hI
    refine ⟨(hF I hI).1, (hF I hI).2.2.1, ?_⟩
    intro x hx
    have hh := (mem_Ico.mp ((hF I hI).2.1 hx)).1
    omega
  have he : ((2 ^ L : ℝ)⁻¹) ^ 3 * (2 ^ L : ℝ) = ((2 ^ L : ℝ)⁻¹) ^ 2 := by field_simp
  calc
    _ ≤ (F.card : ℝ) * (((2 ^ L : ℝ)⁻¹) ^ 3 * (2 ^ L : ℝ)) :=
      PrimitiveNominalMass.primitive_mass_cap F L 3 (by omega) hdata
    _ = (F.card : ℝ) * ((2 ^ L : ℝ)⁻¹) ^ 2 := by rw [he]
    _ ≤ (N : ℝ) ^ (ε / 2) * (((2 : ℝ) ^ C) ^ 2 * (N : ℝ) ^ (-2 : ℝ)) :=
      mul_le_mul hcount (CriticalChannelPowers.nominal_square_upper (by omega) hband) (by positivity) (by positivity)
    _ = ((2 : ℝ) ^ C) ^ 2 * (N : ℝ) ^ (-2 + ε / 2) := by
      rw [mul_left_comm, ← Real.rpow_add hn]
      congr 1
      ring
    _ ≤ (N : ℝ) ^ ((-2 + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.DensePrimitiveTripleRankMass
