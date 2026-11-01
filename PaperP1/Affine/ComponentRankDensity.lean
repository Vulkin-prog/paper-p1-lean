module

public import PaperP1.Affine.PartitionRank
public import PaperP1.Affine.PrivateNullity

/-! # A direct component with small rank density has large size and nullity -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ComponentRankDensity

open Finset PaperP1.Affine PaperP1.SubspaceFamilyRank

theorem nullity_density_bound (l d n r ρ : ℝ) (hl : 0 ≤ l) (hd : 0 < d)
    (hlr : l ≤ r) (hr : r ≤ d * n) (hidentity : r + ρ = n * l) (hρ : 0 ≤ ρ) :
    l / d ≤ n ∧ l ^ 2 / d - l ≤ ρ := by
  have hsize : l / d ≤ n := (div_le_iff₀ hd).mpr (by nlinarith)
  refine ⟨hsize, ?_⟩
  by_cases hdl : d ≤ l
  · have hmul := mul_le_mul_of_nonneg_right hsize (sub_nonneg.mpr hdl)
    have hnullity : n * (l - d) ≤ ρ := by nlinarith
    calc
      _ = (l / d) * (l - d) := by field_simp
      _ ≤ n * (l - d) := hmul
      _ ≤ ρ := hnullity
  · have hld : l ≤ d := by linarith
    have hratio : l ^ 2 / d ≤ l := (div_le_iff₀ hd).mpr (by nlinarith)
    linarith

variable {U ι : Type*} [AddCommGroup U] [Module 𝔽₂ U] [FiniteDimensional 𝔽₂ U]
  [Fintype ι] [DecidableEq ι]
variable (S : ι → Submodule 𝔽₂ U) (P : Finpartition (univ : Finset ι))

theorem exists_part_density (hP : RelationDirectPartition S P) (D : ℝ)
    (hNonempty : Nonempty ι) (hbound : (rank S univ : ℝ) ≤ D * Fintype.card ι) :
    ∃ C : P.parts, (rank S C.val : ℝ) ≤ D * C.val.card := by
  classical
  obtain ⟨i⟩ := hNonempty
  have : Nonempty P.parts := ⟨⟨P.part i, P.part_mem.mpr (mem_univ _)⟩⟩
  have hcard : (∑ C : P.parts, C.val.card) = Fintype.card ι := by
    rw [sum_coe_sort P.parts (fun C : Finset ι ↦ C.card), P.sum_card_parts, card_univ]
  have hcardR : (∑ C : P.parts, (C.val.card : ℝ)) = Fintype.card ι := by exact_mod_cast hcard
  have hrankR : (∑ C : P.parts, (rank S C.val : ℝ)) = rank S univ := by
    exact_mod_cast (rank_partition_sum S P hP).symm
  by_contra hnot
  push Not at hnot
  have hstrict : (∑ C : P.parts, D * (C.val.card : ℝ)) < ∑ C : P.parts, (rank S C.val : ℝ) :=
    sum_lt_sum_of_nonempty univ_nonempty (fun C _ ↦ hnot C)
  rw [← mul_sum, hcardR, hrankR] at hstrict
  linarith

variable [∀ i, Fintype (S i)]

theorem dense_part_bounds (C : P.parts) (L : ℕ) (hL : ∀ i, Module.finrank 𝔽₂ (S i) = L)
    (D : ℝ) (hD : 0 < D) (hdensity : (rank S C.val : ℝ) ≤ D * C.val.card) :
    (rank S C.val : ℝ) / C.val.card ≤ D ∧ (L : ℝ) / D ≤ C.val.card ∧
      (L : ℝ) ^ 2 / D - L ≤ relativeNullityOn S C.val := by
  have hC := P.nonempty_of_mem_parts C.property
  obtain ⟨i, hi⟩ := hC
  have hCpos : (0 : ℝ) < C.val.card := by exact_mod_cast card_pos.mpr ⟨i, hi⟩
  have hlocalNat := local_rank_le S C.val hi
  rw [hL i] at hlocalNat
  have hlocal : (L : ℝ) ≤ rank S C.val := by exact_mod_cast hlocalNat
  have hidentityNat := rank_add_nullity_on S C.val
  have hsum : (∑ i ∈ C.val, Module.finrank 𝔽₂ (S i)) = C.val.card * L := by
    simp only [hL, sum_const, nsmul_eq_mul, Nat.cast_id]
  rw [hsum] at hidentityNat
  have hidentity : (rank S C.val : ℝ) + relativeNullityOn S C.val = (C.val.card : ℝ) * L := by
    exact_mod_cast hidentityNat
  obtain ⟨hsize, hnullity⟩ := nullity_density_bound (L : ℝ) D C.val.card (rank S C.val)
    (relativeNullityOn S C.val) (Nat.cast_nonneg _) hD hlocal hdensity hidentity (Nat.cast_nonneg _)
  exact ⟨(div_le_iff₀ hCpos).mpr (by nlinarith), hsize, hnullity⟩

end PaperP1.ComponentRankDensity
