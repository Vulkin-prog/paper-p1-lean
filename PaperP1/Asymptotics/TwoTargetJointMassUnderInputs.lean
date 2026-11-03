module

public import PaperP1.Model.TwoTargetJointWeight
public import PaperP1.Asymptotics.DensePrimitiveTripleMassUnderInputs

/-! # True joint mass of dense nonaligned or weakly aligned target pairs above arbitrary old sources -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoTargetJointMassUnderInputs

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.SubspaceFamilyRank PaperP1.TwoTargetPrimitiveData PaperP1.FiniteFamilyEnumeration
  PaperP1.TwoTargetWindowSections PaperP1.DensePrimitiveTripleMassUnderInputs

local instance twoTargetJointMassPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) : Module F₂ S := S.module
local instance kernelAddCommGroup {y z L : ℕ} (W : Submodule F₂ (ℕ →₀ F₂)) :
    AddCommGroup (Kernel y z L W) := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := W × squareClassSpace y L × squareClassSpace z L) (Kernel y z L W)

theorem uniform_joint (s : ℕ) (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ θ : ℝ, 0 < θ ∧ ∃ p : Parameters, Hypotheses p →
      ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        ∀ e : Finset ℕ, e.card = s → e ⊆ dyadicBlock N → ∀ P : Finset (ℕ × ℕ),
        (∀ p ∈ P, p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N ∧ p.1 ≠ p.2 ∧ p.1 ∉ e ∧ p.2 ∉ e) →
        (∀ p ∈ P, ¬ CompressedTargetAlignment.Aligned 1 p.1 p.2 L ∨
          (Module.finrank F₂ ↥(squareClassSpace p.1 L ⊓ squareClassSpace p.2 L) : ℝ) ≤ θ * L) →
        (∀ p ∈ P, ∀ B : Finset ℕ, B ⊂ {p.1, p.2} →
          Disjoint (sourceSpace e L) (span (fun x ↦ squareClassSpace x L) B)) →
        (∀ p ∈ P, η * L ≤ (Module.finrank F₂ ↥(sourceSpace e L ⊓
          span (fun x ↦ squareClassSpace x L) {p.1, p.2}) : ℝ)) →
        (∑ p ∈ P, infiniteJointMoment L (TwoTargetFamilyCover.family e p)) ≤
          infiniteJointMoment L e * (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨θ, hθ, t₁, D₁, k₁, t₂, k₂, t₃, D₂, k₃, t₄, k₄,
      _ht₁, _hD₁, _ht₂, _hk₂, _ht₃, _hD₂, _ht₄, _hk₄, hp⟩ :=
    TwoTargetDenseMass.uniform_mass s C η ε hη hε
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨θ, hθ, ⟨t₁, D₁, k₁, t₂, k₂, t₃, D₂, k₃, t₄, k₄⟩, ?_⟩
  intro hgeo
  obtain ⟨ND, _hND, hd⟩ := hp hgeo.leftSource hgeo.leftOrdinary hgeo.leftSourceCurves
    hgeo.leftOrdinaryCurves hgeo.rightSource hgeo.rightOrdinary hgeo.rightSourceCurves hgeo.rightOrdinaryCurves
  refine ⟨3 + ND + NG, by omega, ?_⟩
  intro N hN L hband e hecard heG P hP hadmiss hproper hdense
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hmass := hd N (by omega) L hband (centres e hecard) (centres_mem _ e hecard heG)
    (sourceSpace e L) (source_enumeration e L hecard).le P
    (fun p hp ↦ ⟨(hP p hp).1, (hP p hp).2.1⟩) hadmiss (by
      intro p hp
      have hneq := (hP p hp).2.2.1
      have hcard : ({p.1, p.2} : Finset ℕ).card = 2 := card_pair hneq
      have hcuts := MinimalSpanCrossing.disjoint_singletons (fun x ↦ squareClassSpace x L)
        (sourceSpace e L) {p.1, p.2} (by omega) (hproper p hp)
      have hdim : (Module.finrank F₂ ↥(sourceSpace e L ⊓ span (fun x ↦ squareClassSpace x L) {p.1, p.2}) : ℝ) ≤
          Module.finrank F₂ (Kernel p.1 p.2 L (sourceSpace e L)) := by
        exact_mod_cast TwoTargetJointWeight.intersection_le_kernel L e p.1 p.2 hneq
      exact ⟨hcuts p.1 (mem_insert_self _ _), hcuts p.2 (mem_insert_of_mem (mem_singleton_self _)),
        (hdense p hp).trans hdim⟩)
  calc
    _ ≤ ∑ p ∈ P, infiniteJointMoment L e * (infiniteMarginal p.1 L * infiniteMarginal p.2 L *
        (2 ^ Module.finrank F₂ (Kernel p.1 p.2 L (sourceSpace e L)) : ℝ)) := by
      apply sum_le_sum
      intro p hp
      have hx := hP p hp
      exact TwoTargetJointWeight.joint_bound L hL e p.1 p.2 hx.2.2.2.1 hx.2.2.2.2 hx.2.2.1
    _ = infiniteJointMoment L e * ∑ p ∈ P, infiniteMarginal p.1 L * infiniteMarginal p.2 L *
        (2 ^ Module.finrank F₂ (Kernel p.1 p.2 L (sourceSpace e L)) : ℝ) := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass (infiniteJointMoment_nonneg L e)

end PaperP1.TwoTargetJointMassUnderInputs
