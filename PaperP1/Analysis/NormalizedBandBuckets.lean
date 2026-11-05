module

public import PaperP1.Analysis.DyadicGridMargins
public import PaperP1.Analysis.UnitIntervalSubdivision

/-! # Actual finite buckets inside one dyadic endpoint band -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NormalizedBandBuckets

open Set DyadicGridMargins


def index (M : ℕ) (δ d : ℝ) : ℕ := UnitIntervalSubdivision.index M (d / δ - 1)

theorem normalized_mem (δ d : ℝ) (hδ : 0 < δ) (hd : d ∈ Ico δ (2 * δ)) :
    d / δ - 1 ∈ Ico (0 : ℝ) 1 := by
  have hlo : 1 ≤ d / δ := (le_div_iff₀ hδ).mpr (by simpa only [one_mul] using hd.1)
  have hhi : d / δ < 2 := (div_lt_iff₀ hδ).mpr hd.2
  exact ⟨by linarith only [hlo], by linarith only [hhi]⟩

theorem index_lt (M : ℕ) (hM : 0 < M) (δ d : ℝ) (hδ : 0 < δ) (hd : d ∈ Ico δ (2 * δ)) :
    index M δ d < M := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hn := normalized_mem δ d hδ hd
  apply (Nat.floor_lt (mul_nonneg hMR.le hn.1)).mpr
  nlinarith only [hMR, hn.2]

theorem unit_bucket_distance (M : ℕ) (hM : 0 < M) (u v : ℝ)
    (hu : u ∈ Ico (0 : ℝ) 1) (hv : v ∈ Ico (0 : ℝ) 1)
    (he : UnitIntervalSubdivision.index M u = UnitIntervalSubdivision.index M v) :
    |u - v| ≤ 1 / (M : ℝ) := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hul := Nat.floor_le (mul_nonneg hMR.le hu.1)
  have hvl := Nat.floor_le (mul_nonneg hMR.le hv.1)
  have huh := Nat.lt_floor_add_one ((M : ℝ) * u)
  have hvh := Nat.lt_floor_add_one ((M : ℝ) * v)
  change ⌊(M : ℝ) * u⌋₊ = ⌊(M : ℝ) * v⌋₊ at he
  rw [he] at hul huh
  have hd : |(M : ℝ) * (u - v)| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> nlinarith only [hul, hvl, huh, hvh]
  rw [abs_mul, abs_of_pos hMR] at hd
  apply (le_div_iff₀ hMR).mpr
  nlinarith only [hd]

theorem cluster_distance (M : ℕ) (hM : 0 < M) (δ d e : ℝ) (hδ : 0 < δ)
    (hd : d ∈ Ico δ (2 * δ)) (he : e ∈ Ico δ (2 * δ)) (hindex : index M δ d = index M δ e) :
    |d - e| ≤ δ / (M : ℝ) := by
  have hh := unit_bucket_distance M hM (d / δ - 1) (e / δ - 1)
    (normalized_mem δ d hδ hd) (normalized_mem δ e hδ he) hindex
  have hsub : (d / δ - 1) - (e / δ - 1) = (d - e) / δ := by ring
  rw [hsub, abs_div, abs_of_pos hδ] at hh
  exact ((div_le_iff₀ hδ).mp hh).trans_eq (by ring)

theorem side_cluster_distance (M : ℕ) (hM : 0 < M) (δ : ℝ) (hδ : 0 < δ)
    (i : Fin 2) (a b t u : ℝ)
    (ht : sideDistance i a b t ∈ Ico δ (2 * δ))
    (hu : sideDistance i a b u ∈ Ico δ (2 * δ))
    (hindex : index M δ (sideDistance i a b t) = index M δ (sideDistance i a b u)) :
    |t - u| ≤ δ / (M : ℝ) := by
  have hh := cluster_distance M hM δ (sideDistance i a b t) (sideDistance i a b u) hδ ht hu hindex
  rw [sideDistance_abs_sub] at hh
  exact hh

end PaperP1.NormalizedBandBuckets
