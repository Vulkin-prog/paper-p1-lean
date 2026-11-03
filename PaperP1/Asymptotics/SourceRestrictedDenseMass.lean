module

public import PaperP1.Asymptotics.TwoTargetPrimitiveExtensions

/-! # The complete source-restricted primitive-family conclusion of article Lemma15.2 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceRestrictedDenseMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.TwoTargetWindowSections PaperP1.TwoTargetPrimitiveData PaperP1.FiniteFamilyEnumeration

local instance sourceRestrictedDensePrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) : Module F₂ S := S.module
local instance kernelAddCommGroup {y z L : ℕ} (W : Submodule F₂ (ℕ →₀ F₂)) :
    AddCommGroup (Kernel y z L W) := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := W × squareClassSpace y L × squareClassSpace z L) (Kernel y z L W)

theorem article_15_2_source_restricted (r : ℕ) (hr : 3 ≤ r) (C η a ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
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
      ∀ 𝓔 : Finset (Finset ℕ), (∀ E ∈ 𝓔, E.card = r - 2 ∧ E ⊆ dyadicBlock N) →
        (𝓔.card : ℝ) ≤ (N : ℝ) ^ (a + ε / 4) →
      ∀ F : Finset (Finset ℕ),
        (∀ I ∈ F, I ⊆ dyadicBlock N ∧ I.card = r ∧ ConnectedWindowFamilies.Primitive L I ∧
          η * L ≤ (relativeNullityOn (fun x ↦ squareClassSpace x L) I : ℝ)) →
        (∀ I ∈ F, ∃ E ∈ 𝓔, E ⊆ I) →
        PrimitiveWindowMass.mass F L ≤ (N : ℝ) ^ (-(r : ℝ) + 1 + a + ε)) := by
  obtain ⟨t₁, Ds₁, k₁, t₂, k₂, t₃, Ds₂, k₃, t₄, k₄,
      ht₁, hDs₁, ht₂, hk₂, ht₃, hDs₂, ht₄, hk₄, hext⟩ :=
    TwoTargetPrimitiveExtensions.uniform_extensions (r - 2) (by omega) C η (ε / 4) hη (by positivity)
  let M := 2 * (2 : ℝ) ^ C
  obtain ⟨Na, ha⟩ := HalfCountSchedule.factor_absorption (M ^ (r - 2))
    (-(r : ℝ) + 1 + a + ε / 2) (ε / 2) (by positivity)
  refine ⟨t₁, Ds₁, k₁, t₂, k₂, t₃, Ds₂, k₃, t₄, k₄,
    ht₁, hDs₁, ht₂, hk₂, ht₃, hDs₂, ht₄, hk₄, ?_⟩
  intro hCL₁ hCU₁ hPL₁ hPU₁ hCL₂ hCU₂ hPL₂ hPU₂
  obtain ⟨Ne, _hNe, hext⟩ := hext hCL₁ hCU₁ hPL₁ hPU₁ hCL₂ hCU₂ hPL₂ hPU₂
  refine ⟨max 3 (max Na Ne), by omega, ?_⟩
  intro N hN L hband 𝓔 h𝓔 hcard F hF hcover
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hraw := TwoTargetFamilyCover.weighted_cover (dyadicBlock N) 𝓔 F (PrimitiveWindowMass.weight L)
    (PrimitiveWindowMass.weight_nonneg L) (fun I hI ↦ (hF I hI).1) (by
      intro E hE I hI
      have hEI := (h𝓔 E hE).1
      have hIc := (hF I hI).2.1
      omega) hcover
  have hbound (E : Finset ℕ) (hE : E ∈ 𝓔) :
      (∑ p ∈ TwoTargetFamilyCover.pairs (dyadicBlock N) E F,
        PrimitiveWindowMass.weight L (TwoTargetFamilyCover.family E p)) ≤
        (M / N) ^ (r - 2) * (N : ℝ) ^ (-1 + ε / 4) :=
    hext N (by omega) L hband E (h𝓔 E hE).1 (h𝓔 E hE).2 F
      (fun I hI ↦ ⟨(hF I hI).2.2.1, (hF I hI).2.2.2⟩)
  have hfinite : PrimitiveWindowMass.mass F L ≤
      (𝓔.card : ℝ) * ((M / N) ^ (r - 2) * (N : ℝ) ^ (-1 + ε / 4)) := by
    apply hraw.trans
    calc
      _ ≤ ∑ _E ∈ 𝓔, (M / N) ^ (r - 2) * (N : ℝ) ^ (-1 + ε / 4) := sum_le_sum hbound
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  have hrR : ((r - 2 : ℕ) : ℝ) = (r : ℝ) - 2 := by rw [Nat.cast_sub (by omega : 2 ≤ r)]; norm_num
  calc
    _ ≤ (𝓔.card : ℝ) * ((M / N) ^ (r - 2) * (N : ℝ) ^ (-1 + ε / 4)) := hfinite
    _ ≤ (N : ℝ) ^ (a + ε / 4) * ((M / N) ^ (r - 2) * (N : ℝ) ^ (-1 + ε / 4)) :=
      mul_le_mul_of_nonneg_right hcard (by dsimp [M]; positivity)
    _ = M ^ (r - 2) * ((N : ℝ) ^ ((a + ε / 4) + (-1 + ε / 4)) / (N : ℝ) ^ (r - 2)) := by
      rw [Real.rpow_add hNr (a + ε / 4) (-1 + ε / 4), div_pow]
      ring
    _ = M ^ (r - 2) * (N : ℝ) ^ (((a + ε / 4) + (-1 + ε / 4)) - (r - 2 : ℕ)) := by
      rw [Real.rpow_sub hNr, Real.rpow_natCast]
    _ = M ^ (r - 2) * (N : ℝ) ^ (-(r : ℝ) + 1 + a + ε / 2) := by
      congr 1
      rw [hrR]
      congr 1
      ring
    _ ≤ (N : ℝ) ^ ((-(r : ℝ) + 1 + a + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.SourceRestrictedDenseMass
