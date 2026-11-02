module

public import PaperP1.Asymptotics.AllAlignedTargetTripleMass
public import PaperP1.Combinatorics.GraphStarWeights

/-! # A fixed finite family of exact source channels shares one sharp aligned-target mass threshold -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteAlignedTargetTripleMass

open Finset Filter PaperP1.Model.InfiniteStarts

def hosts (F : Finset (ℕ × ℕ)) (J : ℕ × ℕ → ℕ) (N L : ℕ) : Finset (Finset ℕ) :=
  F.biUnion fun ab ↦ AllAlignedTargetTripleMass.hosts N L ab.1 ab.2 (J ab)

def mass (F : Finset (ℕ × ℕ)) (J : ℕ × ℕ → ℕ) (N L : ℕ) : ℝ :=
  ∑ T ∈ hosts F J N L, infiniteJointMoment L T

theorem all_actual_sources (F : Finset (ℕ × ℕ)) (J : ℕ × ℕ → ℕ)
    (hF : ∀ ab ∈ F, 0 < ab.1) (C : ℝ) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ T : Finset ℕ, T.card = 3 →
      (∃ ab ∈ F, Nonempty (AllAlignedTargetTripleMass.Representation N L ab.1 ab.2 (J ab) T)) →
      T ∈ hosts F J N L := by
  have heach (ab : ℕ × ℕ) (hab : ab ∈ F) : ∀ᶠ N : ℕ in atTop, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ T : Finset ℕ, T.card = 3 →
      AllAlignedTargetTripleMass.Representation N L ab.1 ab.2 (J ab) T →
      T ∈ AllAlignedTargetTripleMass.hosts N L ab.1 ab.2 (J ab) := by
    obtain ⟨N₀, _hN₀, hu⟩ := AllAlignedTargetTripleMass.all_actual_sources ab.1 ab.2 (J ab) (hF ab hab) C
    exact eventually_atTop.mpr ⟨N₀, fun N hN ↦ hu N hN⟩
  obtain ⟨NF, hf⟩ := eventually_atTop.mp ((Finset.eventually_all F).mpr heach)
  refine ⟨max 10 NF, by omega, ?_⟩
  intro N hN L hband T hcard hdata
  obtain ⟨ab, hab, ⟨r⟩⟩ := hdata
  exact mem_biUnion.mpr ⟨ab, hab, hf N (by omega) ab hab L hband T hcard r⟩

theorem uniform_mass (F : Finset (ℕ × ℕ)) (J : ℕ × ℕ → ℕ)
    (hF : ∀ ab ∈ F, 0 < ab.1 ∧ ab.1 < ab.2 ∧ ab.2 < 2 * ab.1 ∧ ab.1.Coprime ab.2)
    (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → mass F J N L ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
  have heach (ab : ℕ × ℕ) (hab : ab ∈ F) : ∀ᶠ N : ℕ in atTop, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      AllAlignedTargetTripleMass.mass N L ab.1 ab.2 (J ab) ≤ (N : ℝ) ^ (-41 / 30 + ε / 2) := by
    obtain ⟨ha, horder, hinterior, hcop⟩ := hF ab hab
    obtain ⟨N₀, _hN₀, hu⟩ := AllAlignedTargetTripleMass.uniform_mass ha horder hinterior hcop (J ab) C (ε / 2) (by positivity)
    exact eventually_atTop.mpr ⟨N₀, fun N hN ↦ hu N hN⟩
  obtain ⟨NF, hf⟩ := eventually_atTop.mp ((Finset.eventually_all F).mpr heach)
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption (F.card : ℝ) (-41 / 30 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 10 (max NF NA), by omega, ?_⟩
  intro N hN L hband
  calc
    _ ≤ ∑ ab ∈ F, AllAlignedTargetTripleMass.mass N L ab.1 ab.2 (J ab) :=
      GraphStarWeights.sum_biUnion_le_nonneg F
        (fun ab ↦ AllAlignedTargetTripleMass.hosts N L ab.1 ab.2 (J ab))
        (fun T ↦ infiniteJointMoment L T) (infiniteJointMoment_nonneg L)
    _ ≤ ∑ _ab ∈ F, (N : ℝ) ^ (-41 / 30 + ε / 2) :=
      sum_le_sum (fun ab hab ↦ hf N (by omega) ab hab L hband)
    _ = (F.card : ℝ) * (N : ℝ) ^ (-41 / 30 + ε / 2) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) ^ ((-41 / 30 + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.FiniteAlignedTargetTripleMass
