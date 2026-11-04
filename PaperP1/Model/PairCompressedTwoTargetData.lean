module

public import PaperP1.Model.PairCompressedPrimitiveFamilies
public import PaperP1.Model.TwoTargetPrimitiveData

/-! # The exact two-target kernel above a possibly dependent source pair -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PairCompressedTwoTargetData

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.PairCompressedPrimitiveFamilies PaperP1.SubspaceFamilyRank
  PaperP1.TwoTargetWindowSections

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) : Module F₂ S := S.module
local instance kernelAddCommGroup {y z L : ℕ} (W : Submodule F₂ (ℕ →₀ F₂)) :
    AddCommGroup (Kernel y z L W) := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := W × squareClassSpace y L × squareClassSpace z L) (Kernel y z L W)

theorem source_span (xy : ℕ × ℕ) (L : ℕ) :
    squareClassSpace xy.1 L ⊔ squareClassSpace xy.2 L ≤
      ⨆ i, squareClassSpace (![xy.1, xy.2] i) L := by
  exact sup_le (le_iSup (fun i : Fin 2 ↦ squareClassSpace (![xy.1, xy.2] i) L) 0)
    (le_iSup (fun i : Fin 2 ↦ squareClassSpace (![xy.1, xy.2] i) L) 1)

theorem primitive_data {L : ℕ} (xy : ℕ × ℕ) (z : Fin 2 → ℕ) (hp : Primitive xy L z) :
    Disjoint (squareClassSpace xy.1 L ⊔ squareClassSpace xy.2 L) (squareClassSpace (z 0) L) ∧
      Disjoint (squareClassSpace xy.1 L ⊔ squareClassSpace xy.2 L) (squareClassSpace (z 1) L) ∧
      Disjoint (squareClassSpace (z 0) L) (squareClassSpace (z 1) L) ∧
      nullity xy L z = Module.finrank F₂
        (Kernel (z 0) (z 1) L (squareClassSpace xy.1 L ⊔ squareClassSpace xy.2 L)) := by
  have hfull : ({1, 2, 0} : Finset (Fin 3)) = univ := by decide
  have hroot : span (spaces xy L z) {0} = squareClassSpace xy.1 L ⊔ squareClassSpace xy.2 L := by
    simp only [span, iSup_unique]
    rfl
  obtain ⟨hWY, hWZ, hYZ, hnull⟩ := TwoTargetPrimitiveCut.primitive_data
    (spaces xy L z) ({0} : Finset (Fin 3)) (1 : Fin 3) (2 : Fin 3)
    (by decide) (by decide) (by decide) (singleton_nonempty _) (by
      intro J hJ
      apply hp.2 J
      simpa only [hfull] using hJ)
  rw [hroot] at hWY hWZ
  change Disjoint (squareClassSpace xy.1 L ⊔ squareClassSpace xy.2 L) (squareClassSpace (z 0) L) at hWY
  change Disjoint (squareClassSpace xy.1 L ⊔ squareClassSpace xy.2 L) (squareClassSpace (z 1) L) at hWZ
  change Disjoint (squareClassSpace (z 0) L) (squareClassSpace (z 1) L) at hYZ
  have hdeficit : nullity xy L z = TwoTargetDensePairs.deficit
      (squareClassSpace xy.1 L ⊔ squareClassSpace xy.2 L) (z 0) (z 1) L := by
    rw [hfull] at hnull
    change nullity xy L z =
      Module.finrank F₂ (span (spaces xy L z) {0}) +
        Module.finrank F₂ (squareClassSpace (z 0) L) + Module.finrank F₂ (squareClassSpace (z 1) L) -
        Module.finrank F₂ ↥(span (spaces xy L z) {0} ⊔
          (squareClassSpace (z 0) L ⊔ squareClassSpace (z 1) L)) at hnull
    rw [hroot] at hnull
    exact hnull
  rw [TwoTargetDensePairs.deficit_eq_kernel ![xy.1, xy.2] L _ (source_span xy L)] at hdeficit
  exact ⟨hWY, hWZ, hYZ, hdeficit⟩

theorem weight_factor {N L : ℕ} (hN : 0 < N) (hL : 0 < L) (xy : ℕ × ℕ) (z : Fin 2 → ℕ)
    (hz : ∀ i, z i ∈ RegularStarts.regularStarts N L) (hp : Primitive xy L z) :
    HomogeneousRunMass.probability L (family xy z) =
      HomogeneousRunMass.probability L {xy.1, xy.2} *
        (infiniteMarginal (z 0) L * infiniteMarginal (z 1) L *
          (2 ^ Module.finrank F₂
            (Kernel (z 0) (z 1) L (squareClassSpace xy.1 L ⊔ squareClassSpace xy.2 L)) : ℝ)) := by
  have hpos (i : Fin 2) : 0 < z i :=
    hN.trans_le (mem_Ico.mp (RegularStarts.regularStarts_subset N L (hz i))).1
  rw [PairCompressedPrimitiveFamilies.weight_factor xy z hz,
    (primitive_data xy z hp).2.2.2,
    RegularStarts.marginal_on_regular (hpos 0) hL (hz 0),
    RegularStarts.marginal_on_regular (hpos 1) hL (hz 1), pow_two]
  ring

end PaperP1.PairCompressedTwoTargetData
