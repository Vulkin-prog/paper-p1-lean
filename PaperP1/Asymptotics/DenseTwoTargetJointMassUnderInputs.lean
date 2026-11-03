module

public import PaperP1.Asymptotics.TwoTargetJointMassUnderInputs
public import PaperP1.Asymptotics.StrongAlignedDenseJointMass

/-! # Every dense minimal pair crossing has true joint cost N⁻¹ without an alignment exception -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DenseTwoTargetJointMassUnderInputs

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.SubspaceFamilyRank PaperP1.TwoTargetPrimitiveData PaperP1.DensePrimitiveTripleMassUnderInputs

theorem uniform_joint (s : ℕ) (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ p : Parameters, Hypotheses p → ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ e : Finset ℕ, e.card = s → e ⊆ dyadicBlock N → ∀ P : Finset (ℕ × ℕ),
      (∀ p ∈ P, p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N ∧ p.1 ≠ p.2 ∧ p.1 ∉ e ∧ p.2 ∉ e) →
      (∀ p ∈ P, ∀ B : Finset ℕ, B ⊂ {p.1, p.2} →
        Disjoint (sourceSpace e L) (span (fun x ↦ squareClassSpace x L) B)) →
      (∀ p ∈ P, η * L ≤ (Module.finrank F₂ ↥(sourceSpace e L ⊓
        span (fun x ↦ squareClassSpace x L) {p.1, p.2}) : ℝ)) →
      (∑ p ∈ P, infiniteJointMoment L (TwoTargetFamilyCover.family e p)) ≤
        infiniteJointMoment L e * (N : ℝ) ^ (-1 + ε) := by
  classical
  obtain ⟨θ, hθ, p, hp⟩ := TwoTargetJointMassUnderInputs.uniform_joint s C η (ε / 2) hη (by positivity)
  obtain ⟨NS, _hNS, hs⟩ := StrongAlignedDenseJointMass.uniform_joint s θ C η (ε / 2) hθ hη (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨p, ?_⟩
  intro hgeo
  obtain ⟨NA, _hNA, ha⟩ := hp hgeo
  refine ⟨3 + NA + NS + NF, by omega, ?_⟩
  intro N hN L hband e hecard heG P hP hproper hdense
  let Q := fun p : ℕ × ℕ ↦ ¬ CompressedTargetAlignment.Aligned 1 p.1 p.2 L ∨
    (Module.finrank F₂ ↥(squareClassSpace p.1 L ⊓ squareClassSpace p.2 L) : ℝ) ≤ θ * L
  let PA := P.filter Q
  let PS := P.filter fun p ↦ ¬ Q p
  have hadmiss : (∑ p ∈ PA, infiniteJointMoment L (TwoTargetFamilyCover.family e p)) ≤
      infiniteJointMoment L e * (N : ℝ) ^ (-1 + ε / 2) :=
    ha N (by omega) L hband e hecard heG PA
      (fun p hp ↦ hP p (mem_filter.mp hp).1) (fun _ hp ↦ (mem_filter.mp hp).2)
      (fun p hp ↦ hproper p (mem_filter.mp hp).1) (fun p hp ↦ hdense p (mem_filter.mp hp).1)
  have hstrong : (∑ p ∈ PS, infiniteJointMoment L (TwoTargetFamilyCover.family e p)) ≤
      infiniteJointMoment L e * (N : ℝ) ^ (-1 + ε / 2) := by
    apply hs N (by omega) L hband e hecard heG PS
    · intro p hp
      obtain ⟨hpP, hn⟩ := mem_filter.mp hp
      obtain ⟨hy, hz, hneq, hyE, hzE⟩ := hP p hpP
      have halign : CompressedTargetAlignment.Aligned 1 p.1 p.2 L := by
        by_contra h
        exact hn (Or.inl h)
      have hlarge : θ * L < (Module.finrank F₂ ↥(squareClassSpace p.1 L ⊓ squareClassSpace p.2 L) : ℝ) :=
        lt_of_not_ge (fun h ↦ hn (Or.inr h))
      exact ⟨hy, hz, hneq, hyE, hzE, halign, hlarge, hdense p hpP⟩
    · intro p hp
      exact hproper p (mem_filter.mp hp).1
  have hsplit := sum_filter_add_sum_filter_not P Q (fun p ↦ infiniteJointMoment L (TwoTargetFamilyCover.family e p))
  change (∑ p ∈ PA, infiniteJointMoment L (TwoTargetFamilyCover.family e p)) +
    (∑ p ∈ PS, infiniteJointMoment L (TwoTargetFamilyCover.family e p)) = _ at hsplit
  have hfactor : 2 * (N : ℝ) ^ (-1 + ε / 2) ≤ (N : ℝ) ^ (-1 + ε) := by
    convert hf N (by omega) using 1
    congr 1
    ring
  have hfactorE := mul_le_mul_of_nonneg_left hfactor (infiniteJointMoment_nonneg L e)
  linarith only [hadmiss, hstrong, hsplit, hfactorE]

end PaperP1.DenseTwoTargetJointMassUnderInputs
