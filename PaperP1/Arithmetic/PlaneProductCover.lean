module

public import PaperP1.Arithmetic.PlaneOffsetCRT
public import PaperP1.Arithmetic.CRTProductCover
public import PaperP1.Analysis.FiniteCRTTails

/-! # Enumerating two group sizes on a finite pool of genuine planes

The third group is not an enumeration label. It will only certify that the
actual center lies on one of the finitely many planes.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PlaneProductCover

open Finset PaperP1.TripleCross

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

abbrev Plane := (Fin 3 → ℤ) × ℤ

def fibre (U : Fin 3 → ℕ) (N : ℕ) (q : Fin 2 → ℕ) (w : Fin 2 → Fin 3 → ℤ)
    (P : Plane) : Finset (Fin 3 → ℕ) :=
  (CRTProductCover.fibre U N q w).filter fun X ↦ P.1 2 ≠ 0 ∧ dot P.1 (fun i ↦ (X i : ℤ)) = P.2

def pairCentres (U : Fin 3 → ℕ) (N R : ℕ) (planes : Finset Plane) (p : ℕ × ℕ) :
    Finset (Fin 3 → ℕ) :=
  (planes ×ˢ CRTProductCover.offsets 2 3 R).biUnion fun c ↦ fibre U N ![p.1, p.2] c.2 c.1

def centres (U : Fin 3 → ℕ) (N R : ℕ) (planes : Finset Plane) (S : Finset (ℕ × ℕ)) :
    Finset (Fin 3 → ℕ) := S.biUnion fun p ↦ pairCentres U N R planes p

theorem mem_fibre (U : Fin 3 → ℕ) (N : ℕ) (q : Fin 2 → ℕ) (w : Fin 2 → Fin 3 → ℤ)
    (P : Plane) (X : Fin 3 → ℕ) : X ∈ fibre U N q w P ↔
      X ∈ CRTProductCover.fibre U N q w ∧ P.1 2 ≠ 0 ∧ dot P.1 (fun i ↦ (X i : ℤ)) = P.2 := mem_filter

theorem fibre_card (U : Fin 3 → ℕ) (N : ℕ) (q : Fin 2 → ℕ) (w : Fin 2 → Fin 3 → ℤ)
    (P : Plane) : (fibre U N q w P).card ≤ (N / (q 0 * q 1) + 1) ^ 2 := by
  by_cases hf : (fibre U N q w P).Nonempty
  · obtain ⟨X₀, hX₀⟩ := hf
    obtain ⟨hX₀, hA, _⟩ := (mem_fibre U N q w P X₀).mp hX₀
    have hcop := ((CRTProductCover.mem_fibre U N q w X₀).mp hX₀).2.1
    have hbound := PlaneOffsetCRT.plane_card (fibre U N q w P) U N q w hcop
      (by
        intro X hX
        exact ((CRTProductCover.mem_fibre U N q w X).mp ((mem_fibre U N q w P X).mp hX).1).1)
      (by
        intro X hX
        exact ((CRTProductCover.mem_fibre U N q w X).mp ((mem_fibre U N q w P X).mp hX).1).2.2)
      P.1 P.2 hA (by intro X hX; exact ((mem_fibre U N q w P X).mp hX).2.2)
    simpa only [Fin.prod_univ_two] using hbound
  · rw [not_nonempty_iff_eq_empty.mp hf, card_empty]
    exact Nat.zero_le _

theorem fibre_real_card (U : Fin 3 → ℕ) (N : ℕ) (q : Fin 2 → ℕ)
    (w : Fin 2 → Fin 3 → ℤ) (P : Plane) :
    ((fibre U N q w P).card : ℝ) ≤ ((N : ℝ) / (q 0 * q 1 : ℕ) + 1) ^ 2 := by
  calc
    _ ≤ ((N / (q 0 * q 1) + 1 : ℕ) : ℝ) ^ 2 := by exact_mod_cast fibre_card U N q w P
    _ ≤ _ := by
      apply pow_le_pow_left₀ (by positivity)
      rw [Nat.cast_add, Nat.cast_one]
      exact add_le_add Nat.cast_div_le le_rfl

theorem mem_pairCentres_of (U : Fin 3 → ℕ) (N R : ℕ) (planes : Finset Plane) (p : ℕ × ℕ)
    (X : Fin 3 → ℕ) (hbox : ∀ i, X i ∈ Ico (U i) (U i + N))
    (P : Plane) (hP : P ∈ planes) (hA : P.1 2 ≠ 0)
    (hplane : dot P.1 (fun i ↦ (X i : ℤ)) = P.2) (w : Fin 2 → Fin 3 → ℤ)
    (hw : ∀ j i, (w j i).natAbs ≤ R)
    (hcop : Pairwise (fun i j ↦ Nat.Coprime (![p.1, p.2] i) (![p.1, p.2] j)))
    (hdiv : ∀ j i, (![p.1, p.2] j : ℤ) ∣ (X i : ℤ) + w j i) :
    X ∈ pairCentres U N R planes p := by
  exact mem_biUnion.mpr ⟨(P, w), mem_product.mpr
    ⟨hP, (CRTProductCover.mem_offsets 2 3 R w).mpr hw⟩,
    (mem_fibre U N _ w P X).mpr
      ⟨(CRTProductCover.mem_fibre U N _ w X).mpr ⟨hbox, hcop, hdiv⟩, hA, hplane⟩⟩

theorem pair_card (U : Fin 3 → ℕ) (N R : ℕ) (planes : Finset Plane) (p : ℕ × ℕ) :
    ((pairCentres U N R planes p).card : ℝ) ≤
      (planes.card : ℝ) * (2 * R + 1 : ℕ) ^ 6 * ((N : ℝ) / (p.1 * p.2 : ℕ) + 1) ^ 2 := by
  have hbound := FiniteCoverCount.cardinal_le (pairCentres U N R planes p)
    (planes ×ˢ CRTProductCover.offsets 2 3 R)
    (fun c ↦ fibre U N ![p.1, p.2] c.2 c.1) (((N : ℝ) / (p.1 * p.2 : ℕ) + 1) ^ 2)
    (fun X hX ↦ mem_biUnion.mp hX) (by
      intro c _
      simpa using fibre_real_card U N ![p.1, p.2] c.2 c.1)
  simpa only [card_product, CRTProductCover.offsets_card, Nat.cast_mul, Nat.cast_pow] using hbound

theorem finite_bound (U : Fin 3 → ℕ) (N R : ℕ) (planes : Finset Plane)
    (S : Finset (ℕ × ℕ)) (T : ℝ) (hT : 1 ≤ T)
    (hS : ∀ p ∈ S, 0 < p.1 ∧ 0 < p.2 ∧ T < (p.1 : ℝ) * p.2) :
    ((centres U N R planes S).card : ℝ) ≤ (planes.card : ℝ) * (2 * R + 1 : ℕ) ^ 6 *
      (2 * IntegerProductTail.productConstant 2 * (N : ℝ) ^ 2 * T ^ (-1 : ℝ) * Real.log (2 * T) +
        2 * S.card) := by
  have hsum : ((centres U N R planes S).card : ℝ) ≤
      (planes.card : ℝ) * (2 * R + 1 : ℕ) ^ 6 * ∑ p ∈ S, ((N : ℝ) / ((p.1 : ℝ) * p.2) + 1) ^ 2 := by
    calc
      _ ≤ ∑ p ∈ S, ((pairCentres U N R planes p).card : ℝ) := by
        exact_mod_cast (card_biUnion_le : (centres U N R planes S).card ≤ _)
      _ ≤ ∑ p ∈ S, (planes.card : ℝ) * (2 * R + 1 : ℕ) ^ 6 *
          ((N : ℝ) / ((p.1 : ℝ) * p.2) + 1) ^ 2 := by
        apply sum_le_sum
        intro p _
        simpa only [Nat.cast_mul] using pair_card U N R planes p
      _ = _ := by rw [mul_sum]
  exact hsum.trans (mul_le_mul_of_nonneg_left (FiniteCRTTails.finite_square_sum N T hT S hS)
    (by positivity))

theorem uniform_bound (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ M ≥ N₀, ∀ (U : Fin 3 → ℕ) (N R : ℕ) (planes : Finset Plane)
      (S : Finset (ℕ × ℕ)) (T V : ℝ), 1 ≤ T → 0 ≤ V →
      (∀ p ∈ S, 0 < p.1 ∧ 0 < p.2 ∧ T < (p.1 : ℝ) * p.2 ∧
        p.1 * p.2 ≤ M ^ K ∧ (p.1 * p.2 : ℕ) ≤ V) →
      ((centres U N R planes S).card : ℝ) ≤ (planes.card : ℝ) * (2 * R + 1 : ℕ) ^ 6 *
        (2 * IntegerProductTail.productConstant 2 * (N : ℝ) ^ 2 * T ^ (-1 : ℝ) * Real.log (2 * T) +
          2 * V * (M : ℝ) ^ ε) := by
  obtain ⟨N₀, hcount⟩ := PositiveProductPairs.uniform_count K ε hε
  refine ⟨N₀, ?_⟩
  intro M hM U N R planes S T V hT hV hS
  have hcard := hcount M hM V hV S (by
    intro p hp
    exact ⟨(hS p hp).1, (hS p hp).2.1, (hS p hp).2.2.2⟩)
  have hf := finite_bound U N R planes S T hT (by
    intro p hp
    exact ⟨(hS p hp).1, (hS p hp).2.1, (hS p hp).2.2.1⟩)
  exact hf.trans (mul_le_mul_of_nonneg_left (by nlinarith [hcard]) (by positivity))

end PaperP1.PlaneProductCover
