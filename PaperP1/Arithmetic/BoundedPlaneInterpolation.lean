module

public import PaperP1.Algebra.TotalDegreeMonomials
public import PaperP1.Algebra.FiniteRowKernel

/-! # A bounded-height equation through the entire actual finite integer population -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BoundedPlaneInterpolation

open Polynomial Finset PaperP1.TotalDegreeMonomials

def entry (D : ℕ) (z : ℤ × ℤ) (i : Index D) : ℤ := z.1 ^ i.val.1.val * z.2 ^ i.val.2.val

def heightBound (D B : ℕ) : ℕ :=
  (3 * Fintype.card (Index D) * (B ^ D + 1)) ^ (Fintype.card (Index D) - 1)

theorem heightBound_polynomial (D B : ℕ) (hB : 1 ≤ B) :
    heightBound D B ≤ (6 * Fintype.card (Index D)) ^ (Fintype.card (Index D) - 1) *
      B ^ (D * (Fintype.card (Index D) - 1)) := by
  have hp : 1 ≤ B ^ D := one_le_pow₀ hB
  have hb : 3 * Fintype.card (Index D) * (B ^ D + 1) ≤
      (6 * Fintype.card (Index D)) * B ^ D := by nlinarith
  calc
    _ ≤ ((6 * Fintype.card (Index D)) * B ^ D) ^ (Fintype.card (Index D) - 1) :=
      Nat.pow_le_pow_left hb _
    _ = _ := by rw [mul_pow, ← pow_mul]

theorem entry_bound (D B : ℕ) (hB : 1 ≤ B) (z : ℤ × ℤ)
    (hx : z.1.natAbs ≤ B) (hy : z.2.natAbs ≤ B) (i : Index D) : (entry D z i).natAbs ≤ B ^ D := by
  simp only [entry, Int.natAbs_mul, Int.natAbs_pow]
  calc
    _ ≤ B ^ i.val.1.val * B ^ i.val.2.val :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hx _) (Nat.pow_le_pow_left hy _)
    _ = B ^ (i.val.1.val + i.val.2.val) := (pow_add _ _ _).symm
    _ ≤ B ^ D := Nat.pow_le_pow_right (by omega) i.property

theorem minor_vanishing (D : ℕ) (P : ℤ[X][X]) (hP : P ≠ 0)
    (hD : PlaneCurvePointCount.degree P ≤ D) (S : Finset (ℤ × ℤ))
    (hzero : ∀ z ∈ S, P.evalEval z.1 z.2 = 0) (f : Index D → S) :
    (Matrix.of (fun i j ↦ entry D (f i).val j)).det = 0 := by
  classical
  let w : Index D → ℤ := fun i ↦ (P.coeff i.val.2.val).coeff i.val.1.val
  have hrec : polynomial D w = P := reconstruction D P hD
  have hw : w ≠ 0 := by
    intro hz
    apply hP
    rw [← hrec, hz]
    simp only [polynomial, Pi.zero_apply, map_zero, Finset.sum_const_zero]
  have hknown (z : S) : ∑ i, entry D z.val i * w i = 0 := by
    have he : (polynomial D w).evalEval z.val.1 z.val.2 = 0 := by rw [hrec]; exact hzero z.val z.property
    rw [evaluation] at he
    calc
      _ = ∑ i : Index D, w i * z.val.1 ^ i.val.1.val * z.val.2 ^ i.val.2.val := by
        apply Finset.sum_congr rfl
        intro i _
        unfold entry
        ring
      _ = 0 := he
  have hv : (Matrix.of (fun i j ↦ entry D (f i).val j)).mulVec w = 0 := by
    funext i
    exact hknown (f i)
  have hsome : ∃ i, w i ≠ 0 := by
    by_contra hn
    apply hw
    funext i
    exact not_not.mp ((not_exists.mp hn) i)
  obtain ⟨i, hi⟩ := hsome
  exact Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors hv
    (mem_nonZeroDivisors_iff_ne_zero.mpr hi)

theorem exists_coefficients (D B : ℕ) (hB : 1 ≤ B) (P : ℤ[X][X]) (hP : P ≠ 0)
    (hD : PlaneCurvePointCount.degree P ≤ D) (S : Finset (ℤ × ℤ))
    (hbox : ∀ z ∈ S, z.1.natAbs ≤ B ∧ z.2.natAbs ≤ B)
    (hzero : ∀ z ∈ S, P.evalEval z.1 z.2 = 0) :
    ∃ w : Index D → ℤ, w ≠ 0 ∧ (∀ i, (w i).natAbs ≤ heightBound D B) ∧
      ∀ z ∈ S, ∑ i, entry D z i * w i = 0 := by
  classical
  have hA (z : S) (i : Index D) : |entry D z.val i| ≤ ((B ^ D + 1 : ℕ) : ℤ) := by
    have hb := entry_bound D B hB z.val (hbox z.val z.property).1 (hbox z.val z.property).2 i
    have hc : ((entry D z.val i).natAbs : ℤ) ≤ ((B ^ D + 1 : ℕ) : ℤ) := by exact_mod_cast (Nat.le_succ_of_le hb)
    simpa only [Int.natCast_natAbs] using hc
  have hm (f : Index D → S) : (Matrix.of (fun i j ↦ (entry D (f i).val j : ℚ))).det = 0 := by
    have hh := congrArg (fun z : ℤ ↦ (z : ℚ)) (minor_vanishing D P hP hD S hzero f)
    rw [Int.cast_det, Int.cast_zero] at hh
    exact hh
  obtain ⟨w, hw, hh, hz⟩ := FiniteRowKernel.exists_integer_annihilator (B ^ D + 1) (by omega)
    (index_card_pos D) (fun z : S ↦ entry D z.val) hA hm
  refine ⟨w, hw, ?_, fun z hzS ↦ hz ⟨z, hzS⟩⟩
  intro i
  have hi : ((w i).natAbs : ℤ) ≤ (heightBound D B : ℤ) := by
    simpa only [Int.natCast_natAbs, heightBound] using hh i
  exact_mod_cast hi

theorem exists_bounded_equation (D B : ℕ) (hB : 1 ≤ B) (P : ℤ[X][X]) (hP : P ≠ 0)
    (hD : PlaneCurvePointCount.degree P ≤ D) (S : Finset (ℤ × ℤ))
    (hbox : ∀ z ∈ S, z.1.natAbs ≤ B ∧ z.2.natAbs ≤ B)
    (hzero : ∀ z ∈ S, P.evalEval z.1 z.2 = 0) :
    ∃ Q : ℤ[X][X], Q ≠ 0 ∧ PlaneCurvePointCount.degree Q ≤ D ∧
      BivariateHeight.height Q ≤ heightBound D B ∧ ∀ z ∈ S, Q.evalEval z.1 z.2 = 0 := by
  obtain ⟨w, hw, hh, hz⟩ := exists_coefficients D B hB P hP hD S hbox hzero
  refine ⟨polynomial D w, ne_zero D w hw, total_degree_le D w, height_le D _ w hh, ?_⟩
  intro z hzS
  rw [evaluation]
  calc
    _ = ∑ i, entry D z i * w i := by
      apply Finset.sum_congr rfl
      intro i _
      unfold entry
      ring
    _ = 0 := hz z hzS

end PaperP1.BoundedPlaneInterpolation
