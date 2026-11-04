module

public import PaperP1.Arithmetic.AsymmetricIntersectionTransport
public import PaperP1.Model.BlockJointIntersection
public import PaperP1.Model.InfiniteTripleCancellation
public import PaperP1.Model.OneTargetCrossing
public import PaperP1.Arithmetic.CompressedSourceBlocks

/-! # Actual joint probabilities controlled by the asymmetric loss -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AsymmetricJointWeight

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.SubspaceFamilyRank PaperP1.AsymmetricEvenLoss

def crossRank (x y z L : ℕ) : ℕ :=
  Module.finrank F₂ ↥((squareClassSpace x L ⊔ squareClassSpace y L) ⊓ squareClassSpace z L)

theorem connected_crossing (L x y z : ℕ) (hzx : z ≠ x) (hzy : z ≠ y)
    (hconn : ConnectedWindowFamilies.Connected L {x, y, z}) : 0 < crossRank x y z L := by
  have hz : z ∉ ({x, y} : Finset ℕ) := by simpa only [mem_insert, mem_singleton, not_or] using And.intro hzx hzy
  have hset : insert z ({x, y} : Finset ℕ) = {x, y, z} :=
    (insert_comm z x {y}).trans (congrArg (insert x) (pair_comm z y))
  have hconn' : ConnectedWindowFamilies.Connected L (insert z ({x, y} : Finset ℕ)) := by
    rwa [hset]
  have hh := OneTargetCrossing.connected_positive {x, y} L z (by simp) hz hconn'
  have hspan : span (fun u ↦ squareClassSpace u L) {x, y} = squareClassSpace x L ⊔ squareClassSpace y L := by
    rw [span_insert]
    simp [span]
  change 0 < Module.finrank F₂ ↥(squareClassSpace z L ⊓ span (fun u ↦ squareClassSpace u L) {x, y}) at hh
  rw [hspan, inf_comm] at hh
  exact hh

theorem upper_bound (L H : ℕ) (hL : 0 < L) (E U : Finset ℕ) (z : ℕ) (hz : z ∉ E)
    (hspace : span (fun x ↦ squareClassSpace x L) E = FiniteEvenSquareClasses.space U) :
    infiniteJointMoment L (E ∪ {z}) ≤ infiniteJointMoment L E * infiniteMarginal z L *
      (2 ^ loss H U z L : ℝ) := by
  have hdis : Disjoint E ({z} : Finset ℕ) := disjoint_singleton_right.mpr hz
  have hh := BlockJointIntersection.upper_bound L hL E {z} hdis
  have hspan : span (fun x ↦ squareClassSpace x L) {z} = squareClassSpace z L := by simp [span]
  rw [hspace, hspan, InfiniteTripleCancellation.singleton_joint] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (AsymmetricIntersectionTransport.intersection_le_loss H U z L))
    (mul_nonneg (infiniteJointMoment_nonneg L E) (MissingBlockProbabilities.infiniteMarginal_nonneg z L)))

theorem crossing_bound (L H : ℕ) (hL : 0 < L) (E U : Finset ℕ) (z : ℕ) (hz : z ∉ E)
    (hspace : span (fun x ↦ squareClassSpace x L) E = FiniteEvenSquareClasses.space U)
    (hcross : 0 < Module.finrank F₂ ↥(span (fun x ↦ squareClassSpace x L) E ⊓ squareClassSpace z L)) :
    infiniteJointMoment L (E ∪ {z}) ≤
      2 * (infiniteJointMoment L E * infiniteMarginal z L) * ((2 ^ loss H U z L : ℝ) - 1) := by
  have hr := AsymmetricIntersectionTransport.intersection_le_loss H U z L
  rw [hspace] at hcross
  have hδ : 1 ≤ loss H U z L := by omega
  have hpow : (2 : ℝ) ≤ 2 ^ loss H U z L := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hδ
  have hpower : (2 ^ loss H U z L : ℝ) ≤ 2 * ((2 ^ loss H U z L : ℝ) - 1) := by linarith only [hpow]
  calc
    _ ≤ (infiniteJointMoment L E * infiniteMarginal z L) * (2 ^ loss H U z L : ℝ) :=
      upper_bound L H hL E U z hz hspace
    _ ≤ (infiniteJointMoment L E * infiniteMarginal z L) * (2 * ((2 ^ loss H U z L : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_left hpower
        (mul_nonneg (infiniteJointMoment_nonneg L E) (MissingBlockProbabilities.infiniteMarginal_nonneg z L))
    _ = _ := by ring

theorem compressed_crossing {N a b L H : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hb : 0 < b)
    (hL : 0 < L) (i j : Fin (L + 1)) {xy : ℕ × ℕ}
    (hxy : xy ∈ DyadicEndpointPairs.sourcePairs N a b L i j) (z : ℕ)
    (hzx : z ≠ xy.1) (hzy : z ≠ xy.2) (hcross : 0 < crossRank xy.1 xy.2 z L) :
    infiniteJointMoment L {xy.1, xy.2, z} ≤
      2 * (infiniteJointMoment L {xy.1, xy.2} * infiniteMarginal z L) *
        ((2 ^ loss H (CompressedSourceBlocks.block N a b L i j (CompressedSourceBlocks.anchor b L i xy)) z L : ℝ) - 1) := by
  have hspan : span (fun x ↦ squareClassSpace x L) {xy.1, xy.2} =
      squareClassSpace xy.1 L ⊔ squareClassSpace xy.2 L := by
    rw [span_insert]
    simp [span]
  have hspace : span (fun x ↦ squareClassSpace x L) {xy.1, xy.2} =
      FiniteEvenSquareClasses.space (CompressedSourceBlocks.block N a b L i j (CompressedSourceBlocks.anchor b L i xy)) := by
    rw [hspan, CompressedSourceBlocks.space_eq hN ha hb i j hxy]
  have hz : z ∉ ({xy.1, xy.2} : Finset ℕ) := by simpa only [mem_insert, mem_singleton, not_or] using And.intro hzx hzy
  have hcross' : 0 < Module.finrank F₂ ↥(span (fun x ↦ squareClassSpace x L) {xy.1, xy.2} ⊓ squareClassSpace z L) := by
    rw [hspan]
    exact hcross
  have hset : ({xy.1, xy.2} : Finset ℕ) ∪ {z} = {xy.1, xy.2, z} := by
    ext v
    simp only [mem_union, mem_insert, mem_singleton]
    tauto
  simpa only [hset] using crossing_bound L H hL {xy.1, xy.2}
    (CompressedSourceBlocks.block N a b L i j (CompressedSourceBlocks.anchor b L i xy)) z hz hspace hcross'

end PaperP1.AsymmetricJointWeight
