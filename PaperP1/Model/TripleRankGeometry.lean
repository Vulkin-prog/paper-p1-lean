module

public import PaperP1.Affine.RetainedNullity
public import PaperP1.Model.FreeComponentRank
public import PaperP1.Model.LocalRigidityConsequences
public import PaperP1.Model.JointMonotonicity
public import PaperP1.Model.InfiniteTripleCancellation
public import PaperP1.Asymptotics.CriticalWindowGeometry

/-! # Actual triple nullity and a two-window bound for every larger joint event -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TripleRankGeometry

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.FreeComponentRank PaperP1.RetainedNullity PaperP1.LocalRigidityConsequences

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem insert_third (x y z : ℕ) : (insert z {x, y} : Finset ℕ) = {x, y, z} := by
  ext i
  simp only [mem_insert, mem_singleton]
  tauto

theorem nullity_le_pair (x y z L : ℕ) (hxy : x ≠ y) (hz : 0 < z) :
    relativeNullityOn (fun w ↦ squareClassSpace w L) {x, y, z} ≤ L + pairIntersectionRank x y L := by
  have h := nullity_insert_le (fun w ↦ squareClassSpace w L) z {x, y}
  rw [insert_third, nullity_pair_eq_intersection _ x y hxy] at h
  have hzrank := LocalRunRank.squareClass_rank_le z L hz
  change relativeNullityOn (fun w ↦ squareClassSpace w L) {x, y, z} ≤
    pairIntersectionRank x y L + Module.finrank F₂ (squareClassSpace z L) at h
  omega

theorem nullity_le_min_pair (x y z L : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    relativeNullityOn (fun w ↦ squareClassSpace w L) {x, y, z} ≤
      L + min (pairIntersectionRank x y L) (min (pairIntersectionRank x z L) (pairIntersectionRank y z L)) := by
  have hxyBound := nullity_le_pair x y z L hxy hz
  have hxzBound := nullity_le_pair x z y L hxz hy
  have hyzBound := nullity_le_pair y z x L hyz hx
  have hxzSet : ({x, z, y} : Finset ℕ) = {x, y, z} := by ext i; simp only [mem_insert, mem_singleton]; tauto
  have hyzSet : ({y, z, x} : Finset ℕ) = {x, y, z} := by ext i; simp only [mem_insert, mem_singleton]; tauto
  rw [hxzSet] at hxzBound
  rw [hyzSet] at hyzBound
  omega

theorem third_of_pair (I : Finset ℕ) (hcard : I.card = 3) (x y : ℕ)
    (hx : x ∈ I) (hy : y ∈ I) (hxy : x ≠ y) :
    ∃ z ∈ I, I = {x, y, z} := by
  have hyErase : y ∈ I.erase x := mem_erase.mpr ⟨hxy.symm, hy⟩
  have hc₁ := card_erase_add_one hx
  have hc₂ := card_erase_add_one hyErase
  have hc : ((I.erase x).erase y).card = 1 := by omega
  obtain ⟨z, hz⟩ := card_eq_one.mp hc
  have heq : I = insert x (insert y ((I.erase x).erase y)) := by
    rw [insert_erase hyErase, insert_erase hx]
  rw [hz] at heq
  exact ⟨z, by rw [heq]; simp, heq⟩

theorem set_nullity_le_pair (I : Finset ℕ) (hcard : I.card = 3) (x y L : ℕ)
    (hx : x ∈ I) (hy : y ∈ I) (hxy : x ≠ y) (hpos : ∀ z ∈ I, 0 < z) :
    relativeNullityOn (fun w ↦ squareClassSpace w L) I ≤ L + pairIntersectionRank x y L := by
  obtain ⟨z, hz, heq⟩ := third_of_pair I hcard x y hx hy hxy
  rw [heq]
  exact nullity_le_pair x y z L hxy (hpos z hz)

theorem critical_nominal_marginal_cap (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ x ∈ dyadicBlock N,
        infiniteMarginal x L ≤ 2 * (2 ^ L : ℝ)⁻¹ := by
  obtain ⟨_K, _hK, Nmarg, hmarg⟩ := critical_band_marginals (1 / 2) C (by norm_num)
  obtain ⟨Ngeom, hgeom⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max Nmarg Ngeom, ?_⟩
  intro N hN L hband x hx
  obtain ⟨hNtwo, hBtwo, _⟩ := hgeom N (by omega) L hband
  have hL : 0 < L := by omega
  have hxN := (mem_Ico.mp hx).1
  have hxone : 1 ≤ x := by omega
  have hbase : (1 / 2 : ℝ) * N ≤ ((x - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hxone, Nat.cast_one]
    have hNcast : (2 : ℝ) ≤ N := by exact_mod_cast hNtwo
    have hxcast : (N : ℝ) ≤ x := by exact_mod_cast hxN
    linarith
  by_cases hp : 0 < infiniteMarginal x L
  · obtain ⟨_, hcases, _⟩ := hmarg N (by omega) x L hL hbase hband hp
    rcases hcases with h | h
    · rw [h]
      have hp : 0 < (2 ^ L : ℝ)⁻¹ := by positivity
      linarith
    · exact h.le
  · exact (le_of_not_gt hp).trans (by positivity)

theorem pair_joint_le_rank_mass (x y L : ℕ) (hxy : x ≠ y) (hL : 0 < L)
    (hx : infiniteMarginal x L ≤ 2 * (2 ^ L : ℝ)⁻¹)
    (hy : infiniteMarginal y L ≤ 2 * (2 ^ L : ℝ)⁻¹) :
    infiniteJointMoment L {x, y} ≤
      4 * ((2 ^ L : ℝ)⁻¹) ^ 2 * (2 ^ pairIntersectionRank x y L : ℝ) := by
  classical
  by_cases hq : 0 < infiniteJointMoment L {x, y}
  · let M := x + y + L
    have hcut (w : ℕ) (hw : w ∈ ({x, y} : Finset ℕ)) : w + L ≤ M := by
      obtain rfl | hw := mem_insert.mp hw
      · dsimp [M]; omega
      · have heq := mem_singleton.mp hw; dsimp [M]; omega
    rw [infiniteJointMoment_exact_of_pos M L {x, y} hL hcut hq,
      prod_pair hxy, nullity_pair_eq_intersection _ x y hxy]
    have hprod := mul_le_mul hx hy (PaperP1.MissingBlockProbabilities.infiniteMarginal_nonneg y L)
      (by positivity : 0 ≤ 2 * (2 ^ L : ℝ)⁻¹)
    have hscaled := mul_le_mul_of_nonneg_right hprod
      (show (0 : ℝ) ≤ 2 ^ pairIntersectionRank x y L by positivity)
    change infiniteMarginal x L * infiniteMarginal y L * (2 ^ pairIntersectionRank x y L : ℝ) ≤ _
    nlinarith only [hscaled]
  · exact (le_of_not_gt hq).trans (by positivity)

theorem family_joint_le_rank_mass (I : Finset ℕ) (x y L : ℕ) (hxI : x ∈ I) (hyI : y ∈ I)
    (hxy : x ≠ y) (hL : 0 < L)
    (hx : infiniteMarginal x L ≤ 2 * (2 ^ L : ℝ)⁻¹)
    (hy : infiniteMarginal y L ≤ 2 * (2 ^ L : ℝ)⁻¹) :
    infiniteJointMoment L I ≤
      4 * ((2 ^ L : ℝ)⁻¹) ^ 2 * (2 ^ pairIntersectionRank x y L : ℝ) := by
  have hsub : ({x, y} : Finset ℕ) ⊆ I := by
    intro w hw
    obtain rfl | hw := mem_insert.mp hw
    · exact hxI
    · simpa only [mem_singleton.mp hw] using hyI
  exact (infiniteJointMoment_antitone L hsub).trans (pair_joint_le_rank_mass x y L hxy hL hx hy)

end PaperP1.TripleRankGeometry
