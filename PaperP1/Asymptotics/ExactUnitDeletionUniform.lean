module

public import PaperP1.Arithmetic.ExactUnitDeletion
public import PaperP1.Arithmetic.OffsetNonalignmentOn
public import PaperP1.Asymptotics.CriticalPolynomialScale
public import PaperP1.Asymptotics.CriticalWindowGeometry
public import PaperP1.Coding.LocalRigidityRegimes

/-! # Uniform deletion of exact alignments for three windows with small proper intersections

All ordered block pairs are covered. The harmless constant is larger than the
source's unordered-pair constant and fits its theta < eta/100 margin.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ExactUnitDeletionUniform

universe u

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model

theorem uniform_deletion (C θ : ℝ) (hθ : 0 ≤ θ) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ (ι : Type u) [Fintype ι] [DecidableEq ι], Fintype.card ι ≤ 3 →
      ∀ X : ι → ℕ, (∀ i, X i ∈ dyadicBlock N) →
      (∀ i j, i ≠ j → (Module.finrank F₂ ↥(squareClassSpace (X i) L ⊓ squareClassSpace (X j) L) : ℝ) ≤
        θ * ((L + 1 : ℕ) : ℝ)) →
      ∃ D : Finset (ι × Fin (L + 1)), (D.card : ℝ) ≤ 18 * θ * ((L + 1 : ℕ) : ℝ) + 36 ∧
        OffsetNonalignmentOn.NoExactOn X L (fun v ↦ v ∉ D) := by
  obtain ⟨NP, hp⟩ := CriticalPolynomialScale.polynomial_lt_scale C 16 (by norm_num) 3
  obtain ⟨NR, hr⟩ := LocalRigidityRegimes.critical_band_relation_rank_le_one (1 / 2) C (by norm_num)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨3 + NP + NR + NG, by omega, ?_⟩
  intro N hN L hband ι _ _ hι X hX hweak
  classical
  have hgeom := hg N (by omega) L hband
  have hlarge : 16 * (L + 1) ^ 3 < N := by exact_mod_cast hp N (by omega) L hband
  have hxB (i : ι) : L + 1 < X i := by have hh := (mem_Ico.mp (hX i)).1; omega
  have hdefect (i : ι) : Module.finrank F₂ (WindowRelationCode.windowRelationCode (X i - 1) (L + 1)) ≤ 1 := by
    have hi := (mem_Ico.mp (hX i)).1
    have hh : N ≤ 2 * (X i - 1) := by omega
    have hhR : (N : ℝ) ≤ 2 * ((X i - 1 : ℕ) : ℝ) := by exact_mod_cast hh
    exact hr N (by omega) (X i - 1) L (by nlinarith only [hhR]) hband
  have hpair (p : ι × ι) : ∃ A B : Finset (Fin (L + 1)),
      ((A.card + B.card : ℕ) : ℝ) ≤ 2 * θ * ((L + 1 : ℕ) : ℝ) + 4 ∧
      (p.1 ≠ p.2 → ExactUnitDeletion.NoExactAway (X p.1) (X p.2) L A B) := by
    by_cases he : p.1 = p.2
    · refine ⟨∅, ∅, ?_, fun hne ↦ False.elim (hne he)⟩
      simp only [card_empty, zero_add, Nat.cast_zero]
      positivity
    · obtain ⟨A, B, hcard, hno⟩ := ExactUnitDeletion.pair_deletion N (X p.1) (X p.2) L
        (by omega) (hX p.1) (hX p.2) (hxB p.1) (hxB p.2) hlarge (hdefect p.1)
      refine ⟨A, B, ?_, fun _hne ↦ hno⟩
      have hc : ((A.card + B.card : ℕ) : ℝ) ≤
          2 * ((Module.finrank F₂ ↥(squareClassSpace (X p.1) L ⊓ squareClassSpace (X p.2) L) : ℝ) + 2) := by
        exact_mod_cast hcard
      have hh := hweak p.1 p.2 he
      linarith only [hc, hh]
  choose A B hcard hno using hpair
  let F := fun p : ι × ι ↦ ((A p).image fun v ↦ (p.1, v)) ∪ ((B p).image fun v ↦ (p.2, v))
  let D := (univ : Finset (ι × ι)).biUnion F
  have hleft (i j : ι) (v : Fin (L + 1)) (hv : v ∈ A (i, j)) : (i, v) ∈ D :=
    mem_biUnion.mpr ⟨(i, j), mem_univ _, mem_union_left _ (mem_image.mpr ⟨v, hv, rfl⟩)⟩
  have hright (i j : ι) (v : Fin (L + 1)) (hv : v ∈ B (i, j)) : (j, v) ∈ D :=
    mem_biUnion.mpr ⟨(i, j), mem_univ _, mem_union_right _ (mem_image.mpr ⟨v, hv, rfl⟩)⟩
  have hboundF (p : ι × ι) : (F p).card ≤ (A p).card + (B p).card :=
    (card_union_le _ _).trans (Nat.add_le_add card_image_le card_image_le)
  have hιR : ((Fintype.card (ι × ι) : ℕ) : ℝ) ≤ 9 := by
    rw [Fintype.card_prod]
    have hh : Fintype.card ι * Fintype.card ι ≤ 9 := by nlinarith only [hι]
    exact_mod_cast hh
  refine ⟨D, ?_, ?_⟩
  · calc
      (D.card : ℝ) ≤ ∑ p : ι × ι, ((F p).card : ℝ) := by exact_mod_cast card_biUnion_le
      _ ≤ ∑ p : ι × ι, (((A p).card + (B p).card : ℕ) : ℝ) := by
        apply sum_le_sum
        intro p _hp
        exact_mod_cast hboundF p
      _ ≤ ∑ _p : ι × ι, (2 * θ * ((L + 1 : ℕ) : ℝ) + 4) := sum_le_sum fun p _hp ↦ hcard p
      _ = ((Fintype.card (ι × ι) : ℕ) : ℝ) * (2 * θ * ((L + 1 : ℕ) : ℝ) + 4) := by
        rw [sum_const, nsmul_eq_mul, card_univ]
      _ ≤ 9 * (2 * θ * ((L + 1 : ℕ) : ℝ) + 4) := mul_le_mul_of_nonneg_right hιR (by positivity)
      _ = _ := by ring
  · intro i j hij u₁ u₂ v₁ v₂ hu₁ hu₂ hv₁ hv₂ hne
    exact hno (i, j) hij u₁ u₂ v₁ v₂
      (fun h ↦ hu₁ (hleft i j u₁ h)) (fun h ↦ hu₂ (hleft i j u₂ h))
      (fun h ↦ hv₁ (hright i j v₁ h)) (fun h ↦ hv₂ (hright i j v₂ h)) hne

end PaperP1.ExactUnitDeletionUniform
