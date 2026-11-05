module

public import PaperP1.Asymptotics.LargePositiveCoreTail
public import PaperP1.Asymptotics.FixedPositiveCoreMass

/-! # Companion T16.2 at every actual cardinality, with the stronger positive-core exponent1 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AllCardinalityCoreMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.RelationCoreWitnesses

theorem uniform_bound (t : ℕ) (η v C ε : ℝ) (htEven : Even t) (ht : 2 ≤ t)
    (hη : 0 ≤ η) (htη : η + 2 ≤ t) (hv : 0 < v) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        ∀ G : Finset ℕ, G ⊆ dyadicBlock N → ∀ F : Finset (Finset ℕ),
        (∀ I ∈ F, I ⊆ G ∧ Core t L I ∧ (L : ℝ) / 2 < runRelativeNullity L I ∧
          (runRelativeNullity L I : ℝ) ≤ η * L) →
        (∑ I ∈ F, v ^ I.card * infiniteJointMoment L I) ≤ (N : ℝ) ^ (-1 + ε) := by
  classical
  obtain ⟨s, hs, NT, _hNT, hlarge⟩ := LargePositiveCoreTail.uniform_joint t η v C (ε / 2)
    htEven ht hη htη hv (by positivity)
  obtain ⟨NW, _hNW, hw⟩ := FixedPositiveCoreMass.uniform_bound s t v C (ε / 2) ht hv (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + NT + NW + NF, by omega, ?_⟩
  intro N hN L hband G hG F hF
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let P := fun I : Finset ℕ ↦ I.card < s
  let FS := F.filter P
  let FT := F.filter fun I ↦ ¬ P I
  have hsmall : (∑ I ∈ FS, v ^ I.card * infiniteJointMoment L I) ≤ (N : ℝ) ^ (-1 + ε / 2) := by
    apply hw N (by omega) L hband G hG FS
    intro I hI
    obtain ⟨hIF, hsize⟩ := mem_filter.mp hI
    obtain ⟨hIG, hcore, hhigh, _hcap⟩ := hF I hIF
    have htwo : 2 ≤ I.card := by
      by_contra hnot
      have hz := RetainedNullity.nullity_card_le_one (fun x ↦ squareClassSpace x L) I (by omega)
      change (L : ℝ) / 2 < (relativeNullityOn (fun x ↦ squareClassSpace x L) I : ℝ) at hhigh
      rw [hz, Nat.cast_zero] at hhigh
      have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
      linarith only [hhigh, hL]
    exact ⟨hIG, htwo, by dsimp only [P] at hsize; omega, hcore, hhigh⟩
  have htail : (∑ I ∈ FT, v ^ I.card * infiniteJointMoment L I) ≤ (N : ℝ) ^ (-1 + ε / 2) := by
    apply (hlarge N (by omega) L hband FT ?_).trans
    · exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [])
    · intro I hI
      obtain ⟨hIF, hsize⟩ := mem_filter.mp hI
      obtain ⟨hIG, hcore, _hhigh, hcap⟩ := hF I hIF
      exact ⟨hIG.trans hG, by dsimp only [P] at hsize; omega, hcore, hcap⟩
  have hsplit := sum_filter_add_sum_filter_not F P (fun I ↦ v ^ I.card * infiniteJointMoment L I)
  change (∑ I ∈ FS, v ^ I.card * infiniteJointMoment L I) +
    (∑ I ∈ FT, v ^ I.card * infiniteJointMoment L I) = _ at hsplit
  have hfactor : 2 * (N : ℝ) ^ (-1 + ε / 2) ≤ (N : ℝ) ^ (-1 + ε) := by
    convert hf N (by omega) using 1
    congr 1
    ring
  linarith only [hsmall, htail, hsplit, hfactor]

theorem companion_T16_2 (t : ℕ) (η v C ε : ℝ) (htEven : Even t) (ht : 2 ≤ t)
    (hη : 0 ≤ η) (htη : η + 2 ≤ t) (hv : 0 < v) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        ∀ G : Finset ℕ, G ⊆ dyadicBlock N → ∀ F : Finset (Finset ℕ),
        (∀ I ∈ F, I ⊆ G ∧ Core t L I ∧ (L : ℝ) / 2 < runRelativeNullity L I ∧
          (runRelativeNullity L I : ℝ) ≤ η * L) →
        (∑ I ∈ F, v ^ I.card * infiniteJointMoment L I) ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
  obtain ⟨N₀, hN₀, h⟩ := uniform_bound t η v C ε htEven ht hη htη hv hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband G hG F hF
  exact (h N hN L hband G hG F hF).trans
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith only []))

end PaperP1.AllCardinalityCoreMass
