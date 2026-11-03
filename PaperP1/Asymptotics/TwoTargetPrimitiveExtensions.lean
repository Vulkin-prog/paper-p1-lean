module

public import PaperP1.Asymptotics.TwoTargetDenseMass
public import PaperP1.Model.TwoTargetPrimitiveData
public import PaperP1.Asymptotics.ActualPairRowActivity

/-! # The exact dense primitive extensions above each actual prescribed source set -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoTargetPrimitiveExtensions

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.TwoTargetWindowSections PaperP1.TwoTargetPrimitiveData PaperP1.FiniteFamilyEnumeration

local instance primitiveExtensionsPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) : Module F₂ S := S.module
local instance kernelAddCommGroup {y z L : ℕ} (W : Submodule F₂ (ℕ →₀ F₂)) :
    AddCommGroup (Kernel y z L W) := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := W × squareClassSpace y L × squareClassSpace z L) (Kernel y z L W)

theorem uniform_extensions (s : ℕ) (hs : 1 ≤ s) (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ t₁ Ds₁ k₁ t₂ k₂ t₃ Ds₂ k₃ t₄ k₄ : ℕ,
      2 ≤ t₁ ∧ 0 < Ds₁ ∧ 2 ≤ t₂ ∧ 1 ≤ k₂ ∧ 2 ≤ t₃ ∧ 0 < Ds₂ ∧ 2 ≤ t₄ ∧ 1 ≤ k₄ ∧
      (UniformSourceSurfaceCover.UniformCover k₁ (t₁ - 1) Ds₁ →
      UniformOrdinarySurfaceCover.UniformCover k₂ (t₂ - 1) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((Ds₁ + 2).choose 2 + k₁) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k₂ + 3) M) →
      UniformSourceSurfaceCover.UniformCover k₃ (t₃ - 1) Ds₂ →
      UniformOrdinarySurfaceCover.UniformCover k₄ (t₄ - 1) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((Ds₂ + 2).choose 2 + k₃) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k₄ + 3) M) →
      ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ E : Finset ℕ, E.card = s → E ⊆ dyadicBlock N →
      ∀ F : Finset (Finset ℕ),
        (∀ I ∈ F, ConnectedWindowFamilies.Primitive L I ∧
          η * L ≤ (relativeNullityOn (fun x ↦ squareClassSpace x L) I : ℝ)) →
        (∑ p ∈ TwoTargetFamilyCover.pairs (dyadicBlock N) E F,
          PrimitiveWindowMass.weight L (TwoTargetFamilyCover.family E p)) ≤
          (2 * (2 : ℝ) ^ C / N) ^ s * (N : ℝ) ^ (-1 + ε)) := by
  obtain ⟨θ, hθ, t₁, Ds₁, k₁, t₂, k₂, t₃, Ds₂, k₃, t₄, k₄,
      ht₁, hDs₁, ht₂, hk₂, ht₃, hDs₂, ht₄, hk₄, hm⟩ :=
    TwoTargetDenseMass.uniform_mass s C η ε hη hε
  obtain ⟨Nm, _hNm, hmarg⟩ := ActualPairRowActivity.uniform_marginal_cap C
  refine ⟨t₁, Ds₁, k₁, t₂, k₂, t₃, Ds₂, k₃, t₄, k₄,
    ht₁, hDs₁, ht₂, hk₂, ht₃, hDs₂, ht₄, hk₄, ?_⟩
  intro hCL₁ hCU₁ hPL₁ hPU₁ hCL₂ hCU₂ hPL₂ hPU₂
  obtain ⟨Nc, _hNc, hc⟩ := hm hCL₁ hCU₁ hPL₁ hPU₁ hCL₂ hCU₂ hPL₂ hPU₂
  refine ⟨max 3 (max Nm Nc), by omega, ?_⟩
  intro N hN L hband E hcard hEG F hF
  have hne : E.Nonempty := card_pos.mp (by omega)
  let P := TwoTargetFamilyCover.pairs (dyadicBlock N) E F
  have hdata (p : ℕ × ℕ) (hp : p ∈ P) :
      Disjoint (sourceSpace E L) (squareClassSpace p.1 L) ∧
      Disjoint (sourceSpace E L) (squareClassSpace p.2 L) ∧
      Disjoint (squareClassSpace p.1 L) (squareClassSpace p.2 L) ∧
      relativeNullityOn (fun x ↦ squareClassSpace x L) (TwoTargetFamilyCover.family E p) =
        Module.finrank F₂ (Kernel p.1 p.2 L (sourceSpace E L)) := by
    obtain ⟨_hy, _hz, hyz, hyE, hzE, hpF⟩ := (TwoTargetFamilyCover.mem_pairs _ E F p).mp hp
    exact primitive_data E hcard hne hyE hzE hyz (hF _ hpF).1
  have hpair := hc N (by omega) L hband (centres E hcard) (centres_mem _ E hcard hEG)
    (sourceSpace E L) (source_enumeration E L hcard).le P (by
      intro p hp
      have h := (TwoTargetFamilyCover.mem_pairs _ E F p).mp hp
      exact ⟨h.1, h.2.1⟩) (by
      intro p hp
      exact TwoTargetAdmissibleDensePairs.of_pair_direct hθ.le (hdata p hp).2.2.1) (by
      intro p hp
      have hmem := (TwoTargetFamilyCover.mem_pairs _ E F p).mp hp
      have hdim := (hF _ hmem.2.2.2.2.2).2
      rw [(hdata p hp).2.2.2] at hdim
      exact ⟨(hdata p hp).1, (hdata p hp).2.1, hdim⟩)
  have hfactor : (∑ p ∈ P, PrimitiveWindowMass.weight L (TwoTargetFamilyCover.family E p)) =
      (∏ x ∈ E, infiniteMarginal x L) *
        ∑ p ∈ P, infiniteMarginal p.1 L * infiniteMarginal p.2 L *
          (2 ^ Module.finrank F₂ (Kernel p.1 p.2 L (sourceSpace E L)) : ℝ) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro p hp
    obtain ⟨_hy, _hz, hyz, hyE, hzE, hpF⟩ := (TwoTargetFamilyCover.mem_pairs _ E F p).mp hp
    exact weight_factor E hcard hne hyE hzE hyz (hF _ hpF).1
  have hcap := source_product_cap E L (2 * (2 : ℝ) ^ C / N)
    (fun x hx ↦ hmarg N (by omega) L hband x (hEG hx))
  rw [hcard] at hcap
  calc
    _ = (∏ x ∈ E, infiniteMarginal x L) *
        ∑ p ∈ P, infiniteMarginal p.1 L * infiniteMarginal p.2 L *
          (2 ^ Module.finrank F₂ (Kernel p.1 p.2 L (sourceSpace E L)) : ℝ) := hfactor
    _ ≤ (∏ x ∈ E, infiniteMarginal x L) * (N : ℝ) ^ (-1 + ε) :=
      mul_le_mul_of_nonneg_left hpair (prod_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)
    _ ≤ _ := mul_le_mul_of_nonneg_right hcap (Real.rpow_nonneg (Nat.cast_nonneg N) _)

end PaperP1.TwoTargetPrimitiveExtensions
