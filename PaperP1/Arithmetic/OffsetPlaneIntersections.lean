module

public import PaperP1.Arithmetic.OffsetPlaneGeometry
public import PaperP1.Algebra.PlaneIntersection
public import Mathlib.Data.Finset.Pi
public import Mathlib.Data.Finset.Prod

/-! # Actual centers on two geometrically distinct offset planes -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OffsetPlaneIntersections

open Finset PaperP1.OffsetPlaneGeometry PaperP1.PlaneIntersection

def centers (N : ℕ) : Finset (Fin 3 → ℕ) := Fintype.piFinset fun _ ↦ Ico N (2 * N)

theorem mem_centers (N : ℕ) (X : Fin 3 → ℕ) : X ∈ centers N ↔ ∀ i, X i ∈ Ico N (2 * N) := by
  simp only [centers, Fintype.mem_piFinset]

def geometry {L : ℕ} (u : Code L) : Set (Fin 3 → ℝ) := plane (planeNormal u) (planeConstant u)

def Distinct {L : ℕ} (u v : Code L) : Prop :=
  planeNormal u ≠ 0 ∧ planeNormal v ≠ 0 ∧ geometry u ≠ geometry v

def family (L : ℕ) : Finset (Set (Fin 3 → ℝ)) := by
  classical
  exact (univ.filter fun u : Code L ↦ planeNormal u ≠ 0).image geometry

theorem mem_family (L : ℕ) (P : Set (Fin 3 → ℝ)) :
    P ∈ family L ↔ ∃ u : Code L, planeNormal u ≠ 0 ∧ geometry u = P := by
  classical
  simp only [family, mem_image, mem_filter, mem_univ, true_and]

theorem family_card_le (L : ℕ) : (family L).card ≤ (L + 1) ^ 9 := by
  classical
  exact (card_image_le.trans (card_le_univ _)).trans_eq (card_codes L)

theorem geometry_contains_iff {L : ℕ} (u : Code L) (X : Fin 3 → ℕ) :
    (fun i ↦ (X i : ℝ)) ∈ geometry u ↔ Contains u X := by
  change realDot (planeNormal u) (fun i ↦ (X i : ℝ)) = (planeConstant u : ℝ) ↔ _
  have hcast : (fun i ↦ (X i : ℝ)) = (fun i ↦ ((X i : ℤ) : ℝ)) := by ext i; simp
  rw [hcast, realDot_int_cast]
  exact Int.cast_inj

def intersection {L : ℕ} (N : ℕ) (u v : Code L) : Finset (Fin 3 → ℕ) := by
  classical
  exact (centers N).filter fun X ↦ Contains u X ∧ Contains v X

theorem mem_intersection {L : ℕ} (N : ℕ) (u v : Code L) (X : Fin 3 → ℕ) :
    X ∈ intersection N u v ↔ (∀ i, X i ∈ Ico N (2 * N)) ∧ Contains u X ∧ Contains v X := by
  classical
  simp only [intersection, mem_filter, mem_centers]

theorem intersection_card_le {L : ℕ} (N : ℕ) (u v : Code L) (hne : Distinct u v) :
    (intersection N u v).card ≤ N := by
  classical
  by_cases hS : (intersection N u v).Nonempty
  · obtain ⟨X₀, hX₀⟩ := hS
    obtain ⟨_, hu₀, hv₀⟩ := (mem_intersection N u v X₀).mp hX₀
    have hcross := cross_ne_zero_of_distinct_meeting (planeNormal u) (planeNormal v)
      (fun i ↦ (X₀ i : ℤ)) (planeConstant u) (planeConstant v) hne.1 hne.2.1 hne.2.2 hu₀ hv₀
    obtain ⟨i, hi⟩ := exists_nonzero_coordinate _ hcross
    have hcard : (intersection N u v).card ≤ (Ico N (2 * N)).card := by
      apply card_le_card_of_injOn (fun X ↦ X i)
      · intro X hX
        exact ((mem_intersection N u v X).mp hX).1 i
      · intro X hX Y hY hcoord
        obtain ⟨_, huX, hvX⟩ := (mem_intersection N u v X).mp hX
        obtain ⟨_, huY, hvY⟩ := (mem_intersection N u v Y).mp hY
        have heq := points_eq_of_coordinate (planeNormal u) (planeNormal v)
          (fun j ↦ (X j : ℤ)) (fun j ↦ (Y j : ℤ)) (planeConstant u) (planeConstant v) i hi
          huX hvX huY hvY (by exact_mod_cast hcoord)
        funext j
        exact_mod_cast congrFun heq j
    simpa only [Nat.card_Ico, show 2 * N - N = N by omega] using hcard
  · rw [not_nonempty_iff_eq_empty.mp hS, card_empty]
    exact Nat.zero_le N

def codePairs (L : ℕ) : Finset (Code L × Code L) := by
  classical
  exact univ.filter fun z ↦ Distinct z.1 z.2

def doubleCenters (N L : ℕ) : Finset (Fin 3 → ℕ) := by
  classical
  exact (codePairs L).biUnion fun z ↦ intersection N z.1 z.2

theorem mem_doubleCenters (N L : ℕ) (X : Fin 3 → ℕ) :
    X ∈ doubleCenters N L ↔ (∀ i, X i ∈ Ico N (2 * N)) ∧
      ∃ u v : Code L, Distinct u v ∧ Contains u X ∧ Contains v X := by
  classical
  constructor
  · intro hX
    obtain ⟨⟨u, v⟩, huv, hX⟩ := mem_biUnion.mp hX
    obtain ⟨hbox, hu, hv⟩ := (mem_intersection N u v X).mp hX
    exact ⟨hbox, u, v, (mem_filter.mp huv).2, hu, hv⟩
  · rintro ⟨hbox, u, v, huv, hu, hv⟩
    exact mem_biUnion.mpr ⟨(u, v), mem_filter.mpr ⟨mem_univ _, huv⟩,
      (mem_intersection N u v X).mpr ⟨hbox, hu, hv⟩⟩

theorem doubleCenters_card_le (N L : ℕ) : (doubleCenters N L).card ≤ (L + 1) ^ 18 * N := by
  classical
  calc
    _ ≤ ∑ z ∈ codePairs L, (intersection N z.1 z.2).card := card_biUnion_le
    _ ≤ ∑ _z ∈ codePairs L, N := sum_le_sum fun z hz ↦
      intersection_card_le N z.1 z.2 (mem_filter.mp hz).2
    _ = (codePairs L).card * N := by simp
    _ ≤ Fintype.card (Code L × Code L) * N := Nat.mul_le_mul_right N (card_le_univ _)
    _ = (L + 1) ^ 18 * N := by rw [Fintype.card_prod, card_codes, ← pow_add]

end PaperP1.OffsetPlaneIntersections
