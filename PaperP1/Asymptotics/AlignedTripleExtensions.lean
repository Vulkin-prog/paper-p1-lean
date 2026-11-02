module

public import PaperP1.Asymptotics.FiniteAlignedTargetTripleMass
public import PaperP1.Asymptotics.UnorderedSeedMassPropagation

/-! # Actual aligned-triple mass propagates to every fixed larger family size -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AlignedTripleExtensions

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def seeds (F : Finset (ℕ × ℕ)) (J : ℕ × ℕ → ℕ) (N L : ℕ) : Finset (Finset ℕ) :=
  ((dyadicBlock N).powersetCard 3).filter fun T ↦ T ∈ FiniteAlignedTargetTripleMass.hosts F J N L

def families (F : Finset (ℕ × ℕ)) (J : ℕ × ℕ → ℕ) (k N L : ℕ) : Finset (Finset ℕ) :=
  ((dyadicBlock N).powersetCard (3 + k)).filter fun I ↦ ∃ T ∈ seeds F J N L, T ⊆ I

def mass (F : Finset (ℕ × ℕ)) (J : ℕ × ℕ → ℕ) (k N L : ℕ) : ℝ :=
  ∑ I ∈ families F J k N L, infiniteJointMoment L I

theorem seed_data {F : Finset (ℕ × ℕ)} {J : ℕ × ℕ → ℕ} {N L : ℕ} {T : Finset ℕ}
    (hT : T ∈ seeds F J N L) :
    T ⊆ dyadicBlock N ∧ T.card = 3 ∧ T ∈ FiniteAlignedTargetTripleMass.hosts F J N L := by
  obtain ⟨hp, hh⟩ := mem_filter.mp hT
  exact ⟨(mem_powersetCard.mp hp).1, (mem_powersetCard.mp hp).2, hh⟩

theorem family_data {F : Finset (ℕ × ℕ)} {J : ℕ × ℕ → ℕ} {k N L : ℕ} {I : Finset ℕ}
    (hI : I ∈ families F J k N L) :
    I ⊆ dyadicBlock N ∧ I.card = 3 + k ∧ ∃ T ∈ seeds F J N L, T ⊆ I := by
  obtain ⟨hp, hh⟩ := mem_filter.mp hI
  exact ⟨(mem_powersetCard.mp hp).1, (mem_powersetCard.mp hp).2, hh⟩

theorem seeds_mass_le (F : Finset (ℕ × ℕ)) (J : ℕ × ℕ → ℕ) (N L : ℕ) :
    (∑ T ∈ seeds F J N L, infiniteJointMoment L T) ≤ FiniteAlignedTargetTripleMass.mass F J N L := by
  apply sum_le_sum_of_subset_of_nonneg (fun T hT ↦ (seed_data hT).2.2)
  intro T _ _
  exact infiniteJointMoment_nonneg L T

theorem uniform_mass (F : Finset (ℕ × ℕ)) (J : ℕ × ℕ → ℕ)
    (hF : ∀ ab ∈ F, 0 < ab.1 ∧ ab.1 < ab.2 ∧ ab.2 < 2 * ab.1 ∧ ab.1.Coprime ab.2)
    (k : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → mass F J k N L ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
  obtain ⟨NP, hp⟩ := UnorderedSeedMassPropagation.uniform_mass 3 (by norm_num) k C (ε / 3) (by positivity)
  obtain ⟨NT, _hNT, ht⟩ := FiniteAlignedTargetTripleMass.uniform_mass F J hF C (ε / 3) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NC, hc⟩ := HalfCountSchedule.factor_absorption ((3 + k).factorial : ℝ)
    (-41 / 30 + 2 * ε / 3) (ε / 3) (by positivity)
  refine ⟨max 10 (max NP (max NT (max NG NC))), by omega, ?_⟩
  intro N hN L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < L := by have hh := (hg N (by omega) L hband).2.2.1; omega
  have hprop := hp N (by omega) L hL hband (seeds F J N L) (fun T hT ↦
    ⟨(seed_data hT).1, (seed_data hT).2.1⟩) (families F J k N L) (fun I hI ↦ family_data hI)
  calc
    _ ≤ ((3 + k).factorial : ℝ) * (N : ℝ) ^ (ε / 3) * ∑ T ∈ seeds F J N L, infiniteJointMoment L T := hprop
    _ ≤ ((3 + k).factorial : ℝ) * (N : ℝ) ^ (ε / 3) * (N : ℝ) ^ (-41 / 30 + ε / 3) :=
      mul_le_mul_of_nonneg_left ((seeds_mass_le F J N L).trans (ht N (by omega) L hband)) (by positivity)
    _ = ((3 + k).factorial : ℝ) * (N : ℝ) ^ (-41 / 30 + 2 * ε / 3) := by
      rw [mul_assoc, ← Real.rpow_add hn]
      congr 2
      ring
    _ ≤ (N : ℝ) ^ ((-41 / 30 + 2 * ε / 3) + ε / 3) := hc N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.AlignedTripleExtensions
