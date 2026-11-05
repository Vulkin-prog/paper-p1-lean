module

public import PaperP1.Asymptotics.NongoodPairJointMass
public import PaperP1.Asymptotics.TwoDependentPairJointMass
public import PaperP1.Asymptotics.CompressedPairMass
public import PaperP1.Asymptotics.AllPrimitiveMass
public import PaperP1.Model.RetainedActivationSeeds
public import PaperP1.Model.RetainedModifiedLaw

/-! # Companion T15.2: an actual measurable exceptional event with rate four-fifths and the literal retained direct sum -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RetainedExceptionalEvent

open Finset MeasureTheory PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.Model.InfiniteRademacher PaperP1.RetainedActiveCount PaperP1.RetainedCountCylinder
  PaperP1.GoodEdgeCompression

theorem uniform_badProbability (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      badProbability (8 * (L + 1) : ℕ) N L G ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
  classical
  obtain ⟨NNG, _hNNG, hng⟩ := NongoodPairJointMass.uniform_bound C (ε / 2) (by positivity)
  obtain ⟨NT, _hNT, ht⟩ := TwoDependentPairJointMass.uniform_bound C (ε / 2) (by positivity)
  obtain ⟨NC, _hNC, hc⟩ := CompressedPairMass.uniform_bound 1 C (ε / 2) (by norm_num) (by positivity)
  obtain ⟨NP, _hNP, hp⟩ := AllPrimitiveMass.uniform_rank 1 C (ε / 2) (by norm_num) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 4 (-4 / 5 + ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + NNG + NT + NC + NP + NG + NF, by omega, ?_⟩
  intro N hN L hband G hG
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hpower : (N : ℝ) ^ (-1 + ε / 2) ≤ (N : ℝ) ^ (-4 / 5 + ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [])
  have hNG := hng N (by omega) L hband G hG
  have hT := (ht N (by omega) L hband G hG).trans hpower
  have hC := (hc N (by omega) L hband G hG).trans hpower
  have hP : (∑ I ∈ WeightedPrimitiveMass.families G L 3, infiniteJointMoment L I) ≤
      (N : ℝ) ^ (-4 / 5 + ε / 2) := by
    have hdata : ∀ I ∈ WeightedPrimitiveMass.families G L 3,
        I ⊆ dyadicBlock N ∧ 3 ≤ I.card ∧ ConnectedWindowFamilies.Primitive L I := by
      intro I hI
      obtain ⟨hIG, hsize, hprim⟩ := (WeightedPrimitiveMass.mem_families G I L 3).mp hI
      exact ⟨hIG.trans hG, hsize, hprim⟩
    calc
      _ ≤ WeightedPrimitiveMass.rankMass (WeightedPrimitiveMass.families G L 3) L 1 := by
        apply sum_le_sum
        intro I _hI
        simp only [one_pow, one_mul]
        exact PrimitiveWindowMass.joint_le_weight L hL I
      _ ≤ (N : ℝ) ^ (-1 + ε / 2) := hp N (by omega) L hband _ hdata
      _ ≤ _ := hpower
  have hseed := RetainedActivationSeeds.joint_bound (8 * (L + 1) : ℕ) N L G
  calc
    _ ≤ ∑ I ∈ RetainedActivationSeeds.families (8 * (L + 1) : ℕ) N L G, infiniteJointMoment L I :=
      RetainedActivationSeeds.badProbability_le_mass _ N L G
    _ ≤ 4 * (N : ℝ) ^ (-4 / 5 + ε / 2) := by linarith only [hseed, hNG, hT, hC, hP]
    _ ≤ (N : ℝ) ^ ((-4 / 5 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

theorem uniform_totalVariation (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      AtomicProbability.totalVariation (RetainedModifiedLaw.originalLaw G L)
        (RetainedModifiedLaw.law (8 * (L + 1) : ℕ) N L G) ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
  obtain ⟨N₀, hN₀, h⟩ := uniform_badProbability C ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband G hG
  exact (RetainedModifiedLaw.coupling _ N L G).trans (h N hN L hband G hG)

theorem companion_T15_2 (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      ∃ E : Set InfiniteSample, MeasurableSet E ∧ infiniteRademacherMeasure.real E ≤ (N : ℝ) ^ (-4 / 5 + ε) ∧
      ∀ ω : InfiniteSample, ω ∉ E →
        (Function.Injective (relationAddition (fun i : activeSet G L ω ↦ squareClassSpace i.val L)) ∨
          ∃ e ∈ goodEdges (8 * (L + 1) : ℕ) N L, e ⊆ activeSet G L ω ∧
            CompressedBlocks.Direct (fun x ↦ squareClassSpace x L) e (activeSet G L ω)) ∧
        ∀ I : Finset ℕ, I ⊆ activeSet G L ω → (runRelativeNullity L I : ℝ) ≤ (L : ℝ) / 3 + 1 := by
  classical
  obtain ⟨N₀, hN₀, h⟩ := uniform_badProbability C ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband G hG
  let H : ℝ := (8 * (L + 1) : ℕ)
  let E := {ω : InfiniteSample | ¬retainedActive H N L G ω}
  refine ⟨E, measurable_badEvent H N L G, h N hN L hband G hG, ?_⟩
  intro ω hω
  have hret : retainedActive H N L G ω := by
    by_contra hn
    exact hω hn
  exact ⟨hret, fun I hI ↦ retained_subfamily_nullity_bound H (by omega : 2 ≤ N) G ω hret I hI⟩

end PaperP1.RetainedExceptionalEvent
