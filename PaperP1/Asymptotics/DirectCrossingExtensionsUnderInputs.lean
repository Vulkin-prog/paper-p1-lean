module

public import PaperP1.Model.DirectCrossingTargets
public import PaperP1.Asymptotics.DensePrimitiveTripleMassUnderInputs

/-! # A dense direct minimal crossing has conditional joint cost N⁻¹ above its true old-source mass -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DirectCrossingExtensionsUnderInputs

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.SubspaceFamilyRank PaperP1.TwoTargetPrimitiveData PaperP1.FiniteFamilyEnumeration
  PaperP1.TwoTargetWindowSections PaperP1.DensePrimitiveTripleMassUnderInputs

local instance directExtensionsPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) : Module F₂ S := S.module
local instance kernelAddCommGroup {y z L : ℕ} (W : Submodule F₂ (ℕ →₀ F₂)) :
    AddCommGroup (Kernel y z L W) := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := W × squareClassSpace y L × squareClassSpace z L) (Kernel y z L W)

theorem uniform_extensions (s : ℕ) (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ p : Parameters, Hypotheses p → ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ e B : Finset ℕ, (e ∪ B).card = s → e ∪ B ⊆ dyadicBlock N → Disjoint e B →
      ∀ P : Finset (ℕ × ℕ),
      (∀ p ∈ P, p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N ∧ p.1 ≠ p.2 ∧
        p.1 ∉ e ∪ B ∧ p.2 ∉ e ∪ B) →
      (∀ p ∈ P, runRelativeNullity L (TwoTargetFamilyCover.family B p) = 0 ∧
        (∀ D : Finset ℕ, D ⊂ TwoTargetFamilyCover.family B p →
          Disjoint (span (fun x ↦ squareClassSpace x L) e) (span (fun x ↦ squareClassSpace x L) D)) ∧
        η * L ≤ (MinimalRelativeRelations.nullity (span (fun x ↦ squareClassSpace x L) e)
          (fun x ↦ squareClassSpace x L) (TwoTargetFamilyCover.family B p) : ℝ)) →
      (∑ p ∈ P, infiniteJointMoment L (TwoTargetFamilyCover.family (e ∪ B) p)) ≤
        (infiniteJointMoment L e * ∏ x ∈ B, infiniteMarginal x L) * (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨θ, hθ, t₁, D₁, k₁, t₂, k₂, t₃, D₂, k₃, t₄, k₄,
      _ht₁, _hD₁, _ht₂, _hk₂, _ht₃, _hD₂, _ht₄, _hk₄, hp⟩ :=
    TwoTargetDenseMass.uniform_mass s C η ε hη hε
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨⟨t₁, D₁, k₁, t₂, k₂, t₃, D₂, k₃, t₄, k₄⟩, ?_⟩
  intro hgeo
  obtain ⟨ND, _hND, hd⟩ := hp hgeo.leftSource hgeo.leftOrdinary hgeo.leftSourceCurves
    hgeo.leftOrdinaryCurves hgeo.rightSource hgeo.rightOrdinary hgeo.rightSourceCurves hgeo.rightOrdinaryCurves
  refine ⟨3 + ND + NG, by omega, ?_⟩
  intro N hN L hband e B hcard hEB heB P hP hF
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hdata (p : ℕ × ℕ) (hp : p ∈ P) :
      Disjoint (sourceSpace (e ∪ B) L) (squareClassSpace p.1 L) ∧
        Disjoint (sourceSpace (e ∪ B) L) (squareClassSpace p.2 L) ∧
        Disjoint (squareClassSpace p.1 L) (squareClassSpace p.2 L) ∧
        MinimalRelativeRelations.nullity (span (fun x ↦ squareClassSpace x L) e)
          (fun x ↦ squareClassSpace x L) (TwoTargetFamilyCover.family B p) =
            Module.finrank F₂ (Kernel p.1 p.2 L (sourceSpace (e ∪ B) L)) := by
    have hx := hP p hp
    exact DirectCrossingTargets.data e B hcard hx.2.2.2.1 hx.2.2.2.2 hx.2.2.1
      (hF p hp).1 (hF p hp).2.1
  have hmass := hd N (by omega) L hband (centres (e ∪ B) hcard)
    (centres_mem _ _ hcard hEB) (sourceSpace (e ∪ B) L) (source_enumeration (e ∪ B) L hcard).le
    P (fun p hp ↦ ⟨(hP p hp).1, (hP p hp).2.1⟩) (by
      intro p hp
      exact TwoTargetAdmissibleDensePairs.of_pair_direct hθ.le (hdata p hp).2.2.1) (by
      intro p hp
      have hdim := (hF p hp).2.2
      rw [(hdata p hp).2.2.2] at hdim
      exact ⟨(hdata p hp).1, (hdata p hp).2.1, hdim⟩)
  calc
    _ ≤ ∑ p ∈ P, (infiniteJointMoment L e * ∏ x ∈ B, infiniteMarginal x L) *
        (infiniteMarginal p.1 L * infiniteMarginal p.2 L *
          (2 ^ Module.finrank F₂ (Kernel p.1 p.2 L (sourceSpace (e ∪ B) L)) : ℝ)) := by
      apply sum_le_sum
      intro p hp
      have hx := hP p hp
      exact DirectCrossingTargets.weight_bound e B hcard hL heB hx.2.2.2.1 hx.2.2.2.2 hx.2.2.1
        (hF p hp).1 (hF p hp).2.1
    _ = (infiniteJointMoment L e * ∏ x ∈ B, infiniteMarginal x L) *
        ∑ p ∈ P, infiniteMarginal p.1 L * infiniteMarginal p.2 L *
          (2 ^ Module.finrank F₂ (Kernel p.1 p.2 L (sourceSpace (e ∪ B) L)) : ℝ) := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass (mul_nonneg (infiniteJointMoment_nonneg L e)
      (prod_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L))

end PaperP1.DirectCrossingExtensionsUnderInputs
