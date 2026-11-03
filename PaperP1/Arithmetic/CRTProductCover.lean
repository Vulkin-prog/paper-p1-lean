module

public import PaperP1.Arithmetic.IntegerOffsetCRT
public import PaperP1.Arithmetic.ProductFactorizations
public import PaperP1.Combinatorics.FiniteCoverCount
public import Mathlib.Data.Nat.Cast.Order.Field

/-! # A finite cover of actual center vectors by product and offset certificates -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CRTProductCover

open Finset

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def offsets (k d R : ℕ) : Finset (Fin k → Fin d → ℤ) :=
  Fintype.piFinset fun _ : Fin k ↦ Fintype.piFinset fun _ : Fin d ↦ Icc (-(R : ℤ)) (R : ℤ)

def box (d : ℕ) (U : Fin d → ℕ) (N : ℕ) : Finset (Fin d → ℕ) :=
  Fintype.piFinset fun i ↦ Ico (U i) (U i + N)

def fibre {k d : ℕ} (U : Fin d → ℕ) (N : ℕ) (q : Fin k → ℕ) (w : Fin k → Fin d → ℤ) :
    Finset (Fin d → ℕ) :=
  (box d U N).filter fun X ↦ Pairwise (fun i j ↦ Nat.Coprime (q i) (q j)) ∧
    ∀ j i, (q j : ℤ) ∣ (X i : ℤ) + w j i

def productCentres (k d : ℕ) (U : Fin d → ℕ) (N R Q : ℕ) : Finset (Fin d → ℕ) :=
  ((ProductFactorizations.pool k Q) ×ˢ offsets k d R).biUnion fun c ↦ fibre U N c.1 c.2

theorem mem_offsets (k d R : ℕ) (w : Fin k → Fin d → ℤ) :
    w ∈ offsets k d R ↔ ∀ j i, (w j i).natAbs ≤ R := by
  simp only [offsets, Fintype.mem_piFinset, mem_Icc]
  apply forall_congr'
  intro j
  apply forall_congr'
  intro i
  rw [← abs_le, ← Int.natCast_natAbs]
  exact Int.ofNat_le

theorem offsets_card (k d R : ℕ) : (offsets k d R).card = (2 * R + 1) ^ (d * k) := by
  have hcard : (Icc (-(R : ℤ)) (R : ℤ)).card = 2 * R + 1 := by rw [Int.card_Icc]; omega
  rw [offsets, Fintype.card_piFinset_const, Fintype.card_piFinset_const, hcard, ← pow_mul]

theorem mem_fibre {k d : ℕ} (U : Fin d → ℕ) (N : ℕ) (q : Fin k → ℕ)
    (w : Fin k → Fin d → ℤ) (X : Fin d → ℕ) :
    X ∈ fibre U N q w ↔ (∀ i, X i ∈ Ico (U i) (U i + N)) ∧
      Pairwise (fun i j ↦ Nat.Coprime (q i) (q j)) ∧ ∀ j i, (q j : ℤ) ∣ (X i : ℤ) + w j i := by
  simp only [fibre, mem_filter, box, Fintype.mem_piFinset]

theorem fibre_card {k d : ℕ} (U : Fin d → ℕ) (N : ℕ) (q : Fin k → ℕ)
    (w : Fin k → Fin d → ℤ) :
    (fibre U N q w).card ≤ (N / (∏ j, q j) + 1) ^ d := by
  by_cases hcop : Pairwise (fun i j ↦ Nat.Coprime (q i) (q j))
  · apply IntegerOffsetCRT.box_card d (fibre U N q w) U N q w hcop
    · intro X hX
      exact ((mem_fibre U N q w X).mp hX).1
    · intro X hX
      exact ((mem_fibre U N q w X).mp hX).2.2
  · have he : fibre U N q w = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro X hX
      exact hcop ((mem_fibre U N q w X).mp hX).2.1
    rw [he, card_empty]
    exact Nat.zero_le _

theorem fibre_real_card {k d : ℕ} (U : Fin d → ℕ) (N : ℕ) (q : Fin k → ℕ)
    (w : Fin k → Fin d → ℤ) :
    ((fibre U N q w).card : ℝ) ≤ ((N : ℝ) / (∏ j, q j : ℕ) + 1) ^ d := by
  calc
    _ ≤ ((N / (∏ j, q j) + 1 : ℕ) : ℝ) ^ d := by exact_mod_cast fibre_card U N q w
    _ ≤ _ := by
      apply pow_le_pow_left₀ (by positivity)
      rw [Nat.cast_add, Nat.cast_one]
      exact add_le_add Nat.cast_div_le le_rfl

theorem mem_productCentres (k d : ℕ) (U : Fin d → ℕ) (N R Q : ℕ) (hQ : 0 < Q)
    (X : Fin d → ℕ) : X ∈ productCentres k d U N R Q ↔
      (∀ i, X i ∈ Ico (U i) (U i + N)) ∧ ∃ q : Fin k → ℕ, ∃ w : Fin k → Fin d → ℤ,
        (∏ j, q j = Q) ∧ (∀ j i, (w j i).natAbs ≤ R) ∧
        Pairwise (fun i j ↦ Nat.Coprime (q i) (q j)) ∧ ∀ j i, (q j : ℤ) ∣ (X i : ℤ) + w j i := by
  constructor
  · intro hX
    obtain ⟨⟨q, w⟩, hqw, hX⟩ := mem_biUnion.mp hX
    obtain ⟨hq, hw⟩ := mem_product.mp hqw
    obtain ⟨hbox, hcop, hdiv⟩ := (mem_fibre U N q w X).mp hX
    exact ⟨hbox, q, w, (ProductFactorizations.mem_pool k Q hQ q).mp hq,
      (mem_offsets k d R w).mp hw, hcop, hdiv⟩
  · rintro ⟨hbox, q, w, hprod, hw, hcop, hdiv⟩
    exact mem_biUnion.mpr ⟨(q, w), mem_product.mpr
      ⟨(ProductFactorizations.mem_pool k Q hQ q).mpr hprod, (mem_offsets k d R w).mpr hw⟩,
      (mem_fibre U N q w X).mpr ⟨hbox, hcop, hdiv⟩⟩

theorem product_card (k d : ℕ) (U : Fin d → ℕ) (N R Q : ℕ) (hQ : 0 < Q) :
    ((productCentres k d U N R Q).card : ℝ) ≤
      ((ProductFactorizations.pool k Q).card : ℝ) * (2 * R + 1 : ℕ) ^ (d * k) *
        ((N : ℝ) / Q + 1) ^ d := by
  have hbound := FiniteCoverCount.cardinal_le (productCentres k d U N R Q)
    ((ProductFactorizations.pool k Q) ×ˢ offsets k d R)
    (fun c ↦ fibre U N c.1 c.2) (((N : ℝ) / Q + 1) ^ d)
    (fun X hX ↦ mem_biUnion.mp hX) (by
      intro c hc
      have hprod := (ProductFactorizations.mem_pool k Q hQ c.1).mp (mem_product.mp hc).1
      simpa only [hprod] using fibre_real_card U N c.1 c.2)
  simpa only [card_product, offsets_card, Nat.cast_mul, Nat.cast_pow] using hbound

end PaperP1.CRTProductCover
