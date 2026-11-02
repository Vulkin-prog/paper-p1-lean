module

public import PaperP1.Model.PrivateNormalizedFamilies
public import Mathlib.Tactic.FinCases

/-! # Exact normalized value sets for the rational triple (10t,12t,15t) -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ThreeSlopeProgressions

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.NormalizedWindowSets
  PaperP1.PrivateNormalizedFamilies

def step : Fin 3 → ℕ := ![6, 5, 4]
def multiple : Fin 3 → ℕ := ![10, 12, 15]
def centres (t : ℕ) : Fin 3 → ℕ := fun i ↦ multiple i * t

def progression (T s L : ℕ) : Finset ℕ :=
  ((range L).image fun u ↦ T + s * u) ∪ {T - s}

theorem step_pos (i : Fin 3) : 0 < step i := by fin_cases i <;> norm_num [step]
theorem multiple_pos (i : Fin 3) : 0 < multiple i := by fin_cases i <;> norm_num [multiple]

theorem centres_ge_two {t : ℕ} (ht : 1 ≤ t) (i : Fin 3) : 2 ≤ centres t i := by
  fin_cases i <;> norm_num [centres, multiple] <;> omega

theorem common_product (t : ℕ) (i : Fin 3) : step i * centres t i = 60 * t := by
  fin_cases i <;> norm_num [step, centres, multiple] <;> omega

theorem predecessor_formula (t : ℕ) (i : Fin 3) :
    step i * (centres t i - 1) = 60 * t - step i := by
  rw [Nat.mul_sub_left_distrib, common_product, Nat.mul_one]

theorem internal_formula (t : ℕ) (i : Fin 3) (u : ℕ) :
    step i * (centres t i + u) = 60 * t + step i * u := by
  rw [Nat.mul_add, common_product]

theorem normalized_progression {t : ℕ} (ht : 1 ≤ t) (L : ℕ) (i : Fin 3) :
    normalized (step i) (centres t i) L = progression (60 * t) (step i) L := by
  ext n
  constructor
  · intro hn
    obtain ⟨m, hm, rfl⟩ := mem_image.mp hn
    obtain ⟨v, rfl⟩ := mem_values.mp hm
    rw [startCompleteVertexLabel_eq_offset (by have hh := centres_ge_two ht i; omega)]
    by_cases hv : v.val = 0
    · rw [hv, Nat.add_zero, predecessor_formula]
      exact mem_union_right _ (mem_singleton.mpr rfl)
    · have heq : centres t i - 1 + v.val = centres t i + (v.val - 1) := by
        have hh := centres_ge_two ht i
        omega
      rw [heq, internal_formula]
      exact mem_union_left _ (mem_image.mpr ⟨v.val - 1, mem_range.mpr (by have hh := v.isLt; omega), rfl⟩)
  · intro hn
    obtain hn | hn := mem_union.mp hn
    · obtain ⟨u, hu, rfl⟩ := mem_image.mp hn
      apply mem_image.mpr
      refine ⟨centres t i + u, mem_values.mpr ⟨⟨u + 1, by have hh := mem_range.mp hu; omega⟩, ?_⟩,
        internal_formula t i u⟩
      rw [startCompleteVertexLabel_eq_offset (by have hh := centres_ge_two ht i; omega)]
      dsimp only
      have hh := centres_ge_two ht i
      omega
    · have heq := mem_singleton.mp hn
      subst n
      apply mem_image.mpr
      refine ⟨centres t i - 1, mem_values.mpr ⟨⟨0, by omega⟩, ?_⟩, predecessor_formula t i⟩
      rw [startCompleteVertexLabel_eq_offset (by have hh := centres_ge_two ht i; omega)]
      simp only [Nat.add_zero]

theorem exclusive {t : ℕ} (ht : 1 ≤ t) (L : ℕ) : Exclusive step (centres t) L := by
  intro i j u heq
  rw [predecessor_formula, internal_formula] at heq
  have hs := step_pos i
  have hT : 0 < 60 * t := by omega
  have hlt := Nat.sub_lt hT hs
  omega

theorem common_mem {t L : ℕ} (ht : 1 ≤ t) (hL : 0 < L) (i : Fin 3) :
    60 * t ∈ normalized (step i) (centres t i) L := by
  rw [normalized_progression ht]
  exact mem_union_left _ (mem_image.mpr ⟨0, mem_range.mpr hL, by omega⟩)

theorem pair_internal {T s t L n : ℕ} (hs : 0 < s) (ht : 0 < t) (hneq : s ≠ t)
    (hsT : s ≤ T) (htT : t ≤ T) :
    n ∈ progression T s L ∩ progression T t L ↔
      ∃ u < L, ∃ v < L, T + s * u = n ∧ T + t * v = n := by
  simp only [progression, mem_inter, mem_union, mem_image, mem_range, mem_singleton]
  constructor
  · rintro ⟨(⟨u, hu, hun⟩ | hun), (⟨v, hv, hvn⟩ | hvn)⟩
    · exact ⟨u, hu, v, hv, hun, hvn⟩
    · have hlt := Nat.sub_lt (show 0 < T by omega) ht
      omega
    · have hlt := Nat.sub_lt (show 0 < T by omega) hs
      omega
    · omega
  · rintro ⟨u, hu, v, hv, hun, hvn⟩
    exact ⟨Or.inl ⟨u, hu, hun⟩, Or.inl ⟨v, hv, hvn⟩⟩

theorem inter_six_five {T L : ℕ} (hT : 6 ≤ T) (hL : 1 ≤ L) :
    progression T 6 L ∩ progression T 5 L =
      (range ((L - 1) / 6 + 1)).image (fun m ↦ T + 30 * m) := by
  ext n
  rw [pair_internal (by omega) (by omega) (by omega) hT (by omega)]
  simp only [mem_image, mem_range]
  constructor
  · rintro ⟨u, hu, v, hv, hun, hvn⟩
    refine ⟨v / 6, by omega, ?_⟩
    omega
  · rintro ⟨m, hm, rfl⟩
    exact ⟨5 * m, by omega, 6 * m, by omega, by omega, by omega⟩

theorem inter_six_four {T L : ℕ} (hT : 6 ≤ T) (hL : 1 ≤ L) :
    progression T 6 L ∩ progression T 4 L =
      (range ((L - 1) / 3 + 1)).image (fun m ↦ T + 12 * m) := by
  ext n
  rw [pair_internal (by omega) (by omega) (by omega) hT (by omega)]
  simp only [mem_image, mem_range]
  constructor
  · rintro ⟨u, hu, v, hv, hun, hvn⟩
    refine ⟨v / 3, by omega, ?_⟩
    omega
  · rintro ⟨m, hm, rfl⟩
    exact ⟨2 * m, by omega, 3 * m, by omega, by omega, by omega⟩

theorem inter_five_four {T L : ℕ} (hT : 5 ≤ T) (hL : 1 ≤ L) :
    progression T 5 L ∩ progression T 4 L =
      (range ((L - 1) / 5 + 1)).image (fun m ↦ T + 20 * m) := by
  ext n
  rw [pair_internal (by omega) (by omega) (by omega) hT (by omega)]
  simp only [mem_image, mem_range]
  constructor
  · rintro ⟨u, hu, v, hv, hun, hvn⟩
    refine ⟨v / 5, by omega, ?_⟩
    omega
  · rintro ⟨m, hm, rfl⟩
    exact ⟨4 * m, by omega, 5 * m, by omega, by omega, by omega⟩

theorem inter_three {T L : ℕ} (hT : 6 ≤ T) (hL : 1 ≤ L) :
    (progression T 6 L ∩ progression T 5 L) ∩ progression T 4 L =
      (range ((L - 1) / 15 + 1)).image (fun m ↦ T + 60 * m) := by
  ext n
  rw [inter_six_five hT hL]
  simp only [mem_inter, mem_image, mem_range, progression, mem_union, mem_singleton]
  constructor
  · rintro ⟨⟨m, hm, hmn⟩, (⟨w, hw, hwn⟩ | hwn)⟩
    · exact ⟨w / 15, by omega, by omega⟩
    · have hlt := Nat.sub_lt (show 0 < T by omega) (by omega : 0 < 4)
      omega
  · rintro ⟨m, hm, rfl⟩
    exact ⟨⟨2 * m, by omega, by omega⟩, Or.inl ⟨15 * m, by omega, by omega⟩⟩

end PaperP1.ThreeSlopeProgressions
