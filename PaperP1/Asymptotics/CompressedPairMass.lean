module

public import PaperP1.Asymptotics.ConnectedOneRankOffsetMass
public import PaperP1.Asymptotics.ConnectedFourCoreMass
public import PaperP1.Asymptotics.AllPairDeficit
public import PaperP1.Model.CompressedPairMass

/-! # The whole compressed-pair mass has exponent one for every dependent source pair and every actual cardinality -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompressedPairMass

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.PairPrimitiveCompression PaperP1.CompressedPairMass

theorem uniform_bound (u C ε : ℝ) (hu : 0 < u) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ G : Finset ℕ, G ⊆ dyadicBlock N → mass (pairs G L) L u ≤ (N : ℝ) ^ (-1 + ε) := by
  classical
  obtain ⟨NL, _hNL, hl⟩ := ConnectedOneRankOffsetMass.uniform_bound (2 * u) C (ε / 2) (by positivity) (by positivity)
  obtain ⟨NC, _hNC, hc⟩ := ConnectedFourCoreMass.uniform_bound (2 * u) C (ε / 2) (by positivity) (by positivity)
  obtain ⟨ND, _hND, hd⟩ := AllPairDeficit.article_15_9 u C (ε / 2) hu (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (4 + 2 * u ^ 2) (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + NL + NC + ND + NG + NF, by omega, ?_⟩
  intro N hN L hband G hG
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let F := (pairs G L).image DistinguishedPairWeights.join
  let low := fun I : Finset ℕ ↦ runRelativeNullity L I ≤ L + 2
  let FL := F.filter low
  let FC := F.filter fun I ↦ ¬ low I
  have hdata (I : Finset ℕ) (hI : I ∈ F) :
      I ⊆ G ∧ 3 ≤ I.card ∧ ConnectedWindowFamilies.Connected L I ∧
        (runRelativeNullity L I ≤ L + 2 ∨ RelationCoreWitnesses.Core 4 L I ∧ runRelativeNullity L I ≤ 2 * L) := by
    obtain ⟨pair, hp, rfl⟩ := mem_image.mp hI
    obtain ⟨heG, he, haG, hdep, hprim⟩ := (mem_pairs G L pair).mp hp
    have hpos : ∀ x ∈ pair.1 ∪ pair.2, 0 < x := by
      intro x hx
      have hxN := hG (union_subset heG haG hx)
      have h := (mem_Ico.mp hxN).1
      omega
    exact ⟨union_subset heG haG, size L pair.1 pair.2 he hprim,
      connected L pair.1 pair.2 he hdep hprim, rank_dichotomy L pair.1 pair.2 he hprim hpos⟩
  have hlow : (∑ I ∈ FL, (2 * u) ^ I.card *
      (infiniteJointMoment L I + |infiniteCenteredCoefficient L I|)) ≤ (N : ℝ) ^ (-1 + ε / 2) := by
    apply hl N (by omega) L hband G hG FL
    intro I hI
    obtain ⟨hIF, hcap⟩ := mem_filter.mp hI
    obtain ⟨hIG, hsize, hconn, _⟩ := hdata I hIF
    exact ⟨hIG, hsize, hconn, hcap⟩
  have hcore : (∑ I ∈ FC, (2 * u) ^ I.card *
      (infiniteJointMoment L I + |infiniteCenteredCoefficient L I|)) ≤ (N : ℝ) ^ (-1 + ε / 2) := by
    apply hc N (by omega) L hband G hG FC
    intro I hI
    obtain ⟨hIF, hnot⟩ := mem_filter.mp hI
    obtain ⟨hIG, hsize, hconn, hdich⟩ := hdata I hIF
    have hlarge := hdich.resolve_left hnot
    exact ⟨hIG, hsize, hconn, hlarge⟩
  have hsplit := sum_filter_add_sum_filter_not F low (fun I ↦
    (2 * u) ^ I.card * (infiniteJointMoment L I + |infiniteCenteredCoefficient L I|))
  change (∑ I ∈ FL, (2 * u) ^ I.card * (infiniteJointMoment L I + |infiniteCenteredCoefficient L I|)) +
    (∑ I ∈ FC, (2 * u) ^ I.card * (infiniteJointMoment L I + |infiniteCenteredCoefficient L I|)) = _ at hsplit
  have htotal : (∑ I ∈ F, (2 * u) ^ I.card *
      (infiniteJointMoment L I + |infiniteCenteredCoefficient L I|)) ≤ 2 * (N : ℝ) ^ (-1 + ε / 2) := by
    linarith only [hlow, hcore, hsplit]
  have hdef := (AllPairDeficitMonotonicity.deficit_mono G (dyadicBlock N) hG L u hu.le).trans
    (hd N (by omega) L hband)
  have hpower : (N : ℝ) ^ (-3 / 2 + ε / 2) ≤ (N : ℝ) ^ (-1 + ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [])
  calc
    _ ≤ 2 * (∑ I ∈ F, (2 * u) ^ I.card *
        (infiniteJointMoment L I + |infiniteCenteredCoefficient L I|)) +
          2 * u ^ 2 * AllPairExtensionDeficit.deficit G L u := finite_bound G L hL u hu.le
    _ ≤ (4 + 2 * u ^ 2) * (N : ℝ) ^ (-1 + ε / 2) := by
      have hD := mul_le_mul_of_nonneg_left (hdef.trans hpower) (by positivity : 0 ≤ 2 * u ^ 2)
      nlinarith only [htotal, hD]
    _ ≤ (N : ℝ) ^ ((-1 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

/-- In particular, this retains any source-channel or original-window separation restriction. -/
theorem uniform_subfamily (u C ε : ℝ) (hu : 0 < u) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ G : Finset ℕ, G ⊆ dyadicBlock N → ∀ P : Finset (Finset ℕ × Finset ℕ),
      P ⊆ pairs G L → mass P L u ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨N₀, hN₀, h⟩ := uniform_bound u C ε hu hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband G hG P hP
  exact (mass_mono P (pairs G L) hP L u hu.le).trans (h N hN L hband G hG)

end PaperP1.CompressedPairMass
