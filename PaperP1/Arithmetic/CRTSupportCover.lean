module

public import PaperP1.Arithmetic.CRTProductCover
public import PaperP1.Arithmetic.OffsetFactorSupports

/-! # CRT certificates indexed by a set of factors, without an ordering cost -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CRTSupportCover

open Finset PaperP1.OffsetFactorSupports

def enumeration (A : Finset ℕ) : Fin A.card ≃ A := A.equivFin.symm

def sizes (A : Finset ℕ) (j : Fin A.card) : ℕ := (enumeration A j).val

def centres (base : Fin 3 → ℕ) (width R : ℕ) (A : Finset ℕ) : Finset (Fin 3 → ℕ) :=
  (CRTProductCover.offsets A.card 3 R).biUnion fun w ↦ CRTProductCover.fibre base width (sizes A) w

def certificates (base : Fin 3 → ℕ) (N D R : ℕ) (Y X : ℝ) : Finset (Fin 3 → ℕ) := by
  classical
  exact ((integerSupports Y X).filter fun A ↦ (N : ℝ) < (A.prod id : ℕ)).biUnion
    fun A ↦ centres base (D * N) R A

theorem sizes_mem (A : Finset ℕ) (j : Fin A.card) : sizes A j ∈ A := (enumeration A j).property

theorem sizes_injective (A : Finset ℕ) : Function.Injective (sizes A) := by
  intro i j hij
  exact (enumeration A).injective (Subtype.ext hij)

theorem product_sizes (A : Finset ℕ) : (∏ j, sizes A j) = A.prod id :=
  ((enumeration A).prod_comp (fun g : A ↦ g.val)).trans (prod_coe_sort A id)

theorem mem_centres_of (base : Fin 3 → ℕ) (width R : ℕ) (A : Finset ℕ) (X : Fin 3 → ℕ)
    (hbox : ∀ i, X i ∈ Ico (base i) (base i + width))
    (hcop : ∀ g ∈ A, ∀ h ∈ A, g ≠ h → Nat.Coprime g h)
    (hdiv : ∀ g ∈ A, ∃ w : Fin 3 → ℤ, (∀ i, (w i).natAbs ≤ R) ∧
      ∀ i, (g : ℤ) ∣ (X i : ℤ) + w i) : X ∈ centres base width R A := by
  classical
  have hdata (j : Fin A.card) := hdiv (sizes A j) (sizes_mem A j)
  choose w hw hwd using hdata
  have hcop' : Pairwise (fun i j ↦ Nat.Coprime (sizes A i) (sizes A j)) := by
    intro i j hij
    exact hcop _ (sizes_mem A i) _ (sizes_mem A j) (fun heq ↦ hij (sizes_injective A heq))
  exact mem_biUnion.mpr ⟨w, (CRTProductCover.mem_offsets A.card 3 R w).mpr hw,
    (CRTProductCover.mem_fibre base width (sizes A) w X).mpr ⟨hbox, hcop', hwd⟩⟩

theorem cardinal_bound (base : Fin 3 → ℕ) (width R : ℕ) (A : Finset ℕ) :
    ((centres base width R A).card : ℝ) ≤
      (2 * R + 1 : ℕ) ^ (3 * A.card) * ((width : ℝ) / (A.prod id : ℕ) + 1) ^ 3 := by
  have h := FiniteCoverCount.cardinal_le (centres base width R A)
    (CRTProductCover.offsets A.card 3 R) (fun w ↦ CRTProductCover.fibre base width (sizes A) w)
    (((width : ℝ) / (A.prod id : ℕ) + 1) ^ 3) (fun X hX ↦ mem_biUnion.mp hX) (by
      intro w _
      simpa only [product_sizes] using CRTProductCover.fibre_real_card base width (sizes A) w)
  simpa only [CRTProductCover.offsets_card, Nat.cast_pow] using h

theorem short_product_bound (base : Fin 3 → ℕ) (N D R : ℕ) (A : Finset ℕ) (hN : 1 ≤ N)
    (hprod : (N : ℝ) < (A.prod id : ℕ)) :
    ((centres base (D * N) R A).card : ℝ) ≤ (2 * R + 1 : ℕ) ^ (3 * A.card) * (D + 1 : ℝ) ^ 3 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hp : (0 : ℝ) < (A.prod id : ℕ) := hn.trans hprod
  have hdiv : (D * N : ℕ) / ((A.prod id : ℕ) : ℝ) ≤ (D : ℝ) := by
    apply (div_le_iff₀ hp).mpr
    have hmul := mul_le_mul_of_nonneg_left hprod.le (Nat.cast_nonneg D)
    simpa only [Nat.cast_mul] using hmul
  exact (cardinal_bound base (D * N) R A).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) (add_le_add hdiv le_rfl) 3) (by positivity))

theorem certificate_card (base : Fin 3 → ℕ) (N D R : ℕ) (Y X : ℝ) (hN : 1 ≤ N) :
    ((certificates base N D R Y X).card : ℝ) ≤
      (D + 1 : ℝ) ^ 3 * integerWeightedCount Y X (((2 * R + 1 : ℕ) : ℝ) ^ 3) := by
  classical
  let pool := (integerSupports Y X).filter fun A ↦ (N : ℝ) < (A.prod id : ℕ)
  calc
    _ ≤ ∑ A ∈ pool, ((centres base (D * N) R A).card : ℝ) := by
      have hnat : (certificates base N D R Y X).card ≤ ∑ A ∈ pool, (centres base (D * N) R A).card := by
        exact card_biUnion_le
      exact_mod_cast hnat
    _ ≤ ∑ A ∈ pool, (2 * R + 1 : ℕ) ^ (3 * A.card) * (D + 1 : ℝ) ^ 3 :=
      sum_le_sum (fun A hA ↦ short_product_bound base N D R A hN (mem_filter.mp hA).2)
    _ = (D + 1 : ℝ) ^ 3 * ∑ A ∈ pool, (((2 * R + 1 : ℕ) : ℝ) ^ 3) ^ A.card := by
      rw [mul_sum]
      apply sum_congr rfl
      intro A _
      rw [← pow_mul]
      ring
    _ ≤ (D + 1 : ℝ) ^ 3 * ∑ A ∈ integerSupports Y X, (((2 * R + 1 : ℕ) : ℝ) ^ 3) ^ A.card :=
      mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)) (by positivity)
    _ = _ := rfl

end PaperP1.CRTSupportCover
