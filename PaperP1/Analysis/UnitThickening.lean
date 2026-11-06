module

public import PaperP1.Analysis.PrimeUnitMean
set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.UnitThickening
open Finset Nat MeasureTheory PaperP1 Filter
open scoped Classical

def thickening (K : ℕ) (B : Finset ℕ) : Set ℝ :=
  ⋃ j ∈ B, Set.Icc ((j : ℝ)-(K : ℝ)-1) ((j : ℝ)-(K : ℝ)+1)

theorem thickening_measurable (K : ℕ) (B : Finset ℕ) : MeasurableSet (thickening K B) :=
  B.measurableSet_biUnion (fun _ _ ↦ measurableSet_Icc)

theorem thickening_measure (K : ℕ) (B : Finset ℕ) : volume.real (thickening K B) ≤ 2*(B.card : ℝ) := by
  have hlen (j : ℕ) : volume.real (Set.Icc ((j : ℝ)-(K : ℝ)-1) ((j : ℝ)-(K : ℝ)+1))=2 := by
    rw [Real.volume_real_Icc_of_le (by linarith)]
    ring
  calc
    _ ≤ ∑ j ∈ B, volume.real (Set.Icc ((j : ℝ)-(K : ℝ)-1) ((j : ℝ)-(K : ℝ)+1)) :=
      measureReal_biUnion_finset_le B _
    _ = _ := by simp only [hlen,sum_const,nsmul_eq_mul]; ring

theorem unit_cover (K : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (-(K : ℝ)-1/2) ((K : ℝ)+1/2)) :
    ∃ j ∈ range (2*K+1), t ∈ Set.Icc ((j : ℝ)-(K : ℝ)-1/2) ((j : ℝ)-(K : ℝ)+1/2) := by
  let x : ℝ := t+(K : ℝ)+1/2
  let j₀ : ℕ := ⌊x⌋₊
  have hx : 0 ≤ x := by dsimp only [x]; linarith [ht.1]
  have hfloor : (j₀ : ℝ) ≤ x := Nat.floor_le hx
  have hceil : x < (j₀ : ℝ)+1 := Nat.lt_floor_add_one x
  by_cases hj : j₀ ≤ 2*K
  · refine ⟨j₀,mem_range.mpr (by omega),?_⟩
    dsimp only [x] at hfloor hceil
    constructor <;> linarith
  · have hjN : 2*K+1 ≤ j₀ := by omega
    have hjR : 2*(K : ℝ)+1 ≤ (j₀ : ℝ) := by exact_mod_cast hjN
    refine ⟨2*K,mem_range.mpr (by omega),?_⟩
    simp only [Nat.cast_mul,Nat.cast_ofNat]
    dsimp only [x] at hfloor
    constructor <;> linarith [ht.2]

theorem thickening_subset (K : ℕ) (B : Finset ℕ) (hB : B ⊆ range (2*K+1)) :
    thickening K B ⊆ Set.Icc (-(K : ℝ)-1) ((K : ℝ)+1) := by
  intro u hu
  obtain ⟨j,huj⟩ := Set.mem_iUnion.mp hu
  obtain ⟨hjB,hu⟩ := Set.mem_iUnion.mp huj
  have hjN : j ≤ 2*K := by have hh := mem_range.mp (hB hjB); omega
  have hjR : (j : ℝ) ≤ 2*(K : ℝ) := by exact_mod_cast hjN
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  constructor <;> linarith [hu.1,hu.2]

theorem good_unit_at_point (K : ℕ) (B : Finset ℕ) (u : ℝ)
    (hu : u ∈ Set.Icc (-(K : ℝ)) (K : ℝ)) (hnot : u ∉ thickening K B) (t : ℝ)
    (ht : t ∈ Set.Icc (u-1/2) (u+1/2)) :
    ∃ j ∈ range (2*K+1), j ∉ B ∧ t ∈ Set.Icc ((j : ℝ)-(K : ℝ)-1/2) ((j : ℝ)-(K : ℝ)+1/2) := by
  obtain ⟨j,hj,hjt⟩ := unit_cover K t (by constructor <;> linarith [hu.1,hu.2,ht.1,ht.2])
  refine ⟨j,hj,?_,hjt⟩
  intro hjB
  apply hnot
  exact Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨hjB,by constructor <;> linarith [ht.1,ht.2,hjt.1,hjt.2]⟩⟩
end PaperP1.UnitThickening
