module

public import PaperP1.Model.PairCompressedTwoTargetData
public import PaperP1.Asymptotics.DensePrimitiveTripleMassUnderInputs

/-! # Dense primitive two-target extensions of the actual compressed source span

No directness of the two original source windows is imposed. The existing
finite geometric inputs precede the threshold and every source pair.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PairCompressedDenseExtensionsUnderInputs

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.PairCompressedPrimitiveFamilies PaperP1.TwoTargetWindowSections

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) : Module F₂ S := S.module
local instance kernelAddCommGroup {y z L : ℕ} (W : Submodule F₂ (ℕ →₀ F₂)) :
    AddCommGroup (Kernel y z L W) := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := W × squareClassSpace y L × squareClassSpace z L) (Kernel y z L W)

theorem uniform_extensions (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ p : DensePrimitiveTripleMassUnderInputs.Parameters,
      DensePrimitiveTripleMassUnderInputs.Hypotheses p →
      ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ xy : ℕ × ℕ, xy.1 ∈ dyadicBlock N → xy.2 ∈ dyadicBlock N →
      ∀ F : Finset (Fin 2 → ℕ),
      (∀ z ∈ F, (∀ i, z i ∈ RegularStarts.regularStarts N L) ∧
        Primitive xy L z ∧ η * L ≤ (nullity xy L z : ℝ)) →
      (∑ z ∈ F, HomogeneousRunMass.probability L (family xy z)) ≤
        HomogeneousRunMass.probability L {xy.1, xy.2} * (N : ℝ) ^ (-1 + ε) := by
  classical
  obtain ⟨θ, hθ, t₁, D₁, k₁, t₂, k₂, t₃, D₂, k₃, t₄, k₄,
      _ht₁, _hD₁, _ht₂, _hk₂, _ht₃, _hD₂, _ht₄, _hk₄, hm⟩ :=
    TwoTargetDenseMass.uniform_mass 2 C η ε hη hε
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨⟨t₁, D₁, k₁, t₂, k₂, t₃, D₂, k₃, t₄, k₄⟩, ?_⟩
  intro hgeo
  obtain ⟨NM, _hNM, hm⟩ := hm hgeo.leftSource hgeo.leftOrdinary hgeo.leftSourceCurves
    hgeo.leftOrdinaryCurves hgeo.rightSource hgeo.rightOrdinary hgeo.rightSourceCurves hgeo.rightOrdinaryCurves
  refine ⟨max 3 (max NG NM), by omega, ?_⟩
  intro N hN L hband xy hx hy F hF
  have hL : 0 < L := by have hh := (hg N (by omega) L hband).2.2.1; omega
  let f := fun z : Fin 2 → ℕ ↦ (z 0, z 1)
  have hinj : Function.Injective f := by
    intro z w heq
    funext i
    fin_cases i
    · exact congrArg Prod.fst heq
    · exact congrArg Prod.snd heq
  let P := F.image f
  let W := squareClassSpace xy.1 L ⊔ squareClassSpace xy.2 L
  have hdata (q : ℕ × ℕ) (hq : q ∈ P) :
      q.1 ∈ dyadicBlock N ∧ q.2 ∈ dyadicBlock N ∧
      Disjoint W (squareClassSpace q.1 L) ∧ Disjoint W (squareClassSpace q.2 L) ∧
      Disjoint (squareClassSpace q.1 L) (squareClassSpace q.2 L) ∧
      η * L ≤ (Module.finrank F₂ (Kernel q.1 q.2 L W) : ℝ) := by
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hq
    obtain ⟨hzR, hp, hρ⟩ := hF z hz
    obtain ⟨hWY, hWZ, hYZ, hnull⟩ := PairCompressedTwoTargetData.primitive_data xy z hp
    exact ⟨RegularStarts.regularStarts_subset N L (hzR 0),
      RegularStarts.regularStarts_subset N L (hzR 1), hWY, hWZ, hYZ, hnull ▸ hρ⟩
  have hpair := hm N (by omega) L hband ![xy.1, xy.2] (by
    intro i
    fin_cases i
    · exact hx
    · exact hy) W (PairCompressedTwoTargetData.source_span xy L) P
    (fun q hq ↦ ⟨(hdata q hq).1, (hdata q hq).2.1⟩)
    (fun q hq ↦ TwoTargetAdmissibleDensePairs.of_pair_direct hθ.le (hdata q hq).2.2.2.2.1)
    (fun q hq ↦ ⟨(hdata q hq).2.2.1, (hdata q hq).2.2.2.1, (hdata q hq).2.2.2.2.2⟩)
  have hfactor : (∑ z ∈ F, HomogeneousRunMass.probability L (family xy z)) =
      HomogeneousRunMass.probability L {xy.1, xy.2} *
        ∑ q ∈ P, infiniteMarginal q.1 L * infiniteMarginal q.2 L *
          (2 ^ Module.finrank F₂ (Kernel q.1 q.2 L W) : ℝ) := by
    rw [mul_sum, sum_image hinj.injOn]
    apply sum_congr rfl
    intro z hz
    exact PairCompressedTwoTargetData.weight_factor (by omega) hL xy z (hF z hz).1 (hF z hz).2.1
  rw [hfactor]
  exact mul_le_mul_of_nonneg_left hpair (HomogeneousRunMass.probability_pos L _).le

end PaperP1.PairCompressedDenseExtensionsUnderInputs
