module

public import PaperP1.Algebra.PlaneNormalRigidity
public import PaperP1.Arithmetic.OffsetLinePopulation

/-! # Rigidity of every two-coordinate projection of three actual windows -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ThreeWindowRigidity

open PaperP1.Arithmetic PaperP1.Affine PaperP1.OffsetLinePopulation PaperP1.TwoPointSquareClasses
  PaperP1.PlaneNormalRigidity

def valueVector {L : ℕ} (X : Fin 3 → ℕ) (v : Fin 3 → Fin (L + 1)) : Fin 3 → ℤ :=
  fun i ↦ (X i : ℤ) + offsetVector v i

theorem valueVector_pos {L : ℕ} (X : Fin 3 → ℕ) (hx : ∀ i, 2 ≤ X i)
    (v : Fin 3 → Fin (L + 1)) (i : Fin 3) : 0 < valueVector X v i := by
  unfold valueVector offsetVector
  have h := hx i
  omega

theorem valueVector_eq_vertex {L : ℕ} (X : Fin 3 → ℕ) (v : Fin 3 → Fin (L + 1))
    (i : Fin 3) (hx : 0 < X i) : valueVector X v i = (startCompleteVertexLabel (X i) L (v i) : ℤ) := by
  rw [startCompleteVertexLabel_eq_offset hx]
  unfold valueVector offsetVector
  omega

theorem valueVector_eq_natural {L : ℕ} (X : Fin 3 → ℕ) (v : Fin 3 → Fin (L + 1))
    (i : Fin 3) (hx : 0 < X i) : valueVector X v i = (PaperP1.SaturationPrimes.value (X i) (v i) : ℤ) := by
  unfold valueVector offsetVector PaperP1.SaturationPrimes.value
  omega

theorem offset_difference_natAbs_le {L : ℕ} (v w : Fin 3 → Fin (L + 1)) (i : Fin 3) :
    (offsetVector v i - offsetVector w i).natAbs ≤ L + 1 := by
  have hv := (v i).isLt
  have hw := (w i).isLt
  have h : |offsetVector v i - offsetVector w i| ≤ ((L + 1 : ℕ) : ℤ) := by
    apply abs_le.mpr
    unfold offsetVector
    omega
  rw [← Int.natCast_natAbs] at h
  exact_mod_cast h

theorem offset_natAbs_le {L : ℕ} (v : Fin 3 → Fin (L + 1)) (i : Fin 3) :
    (offsetVector v i).natAbs ≤ L + 1 := by
  have hv := (v i).isLt
  have h : |offsetVector v i| ≤ ((L + 1 : ℕ) : ℤ) := by
    apply abs_le.mpr
    unfold offsetVector
    omega
  rw [← Int.natCast_natAbs] at h
  exact_mod_cast h

theorem projection_value_eq_of_first_injective {L : ℕ} (X : Fin 3 → ℕ)
    (u : Fin 3 → Fin 3 → Fin (L + 1)) (hx : ∀ i, 2 ≤ X i) (i j : Fin 3)
    (hinj : Function.Injective (evenSquareClassMap (X i) L))
    (hdirect : Disjoint (squareClassSpace (X i) L) (squareClassSpace (X j) L))
    (p q : Fin 3)
    (hcross : valueVector X (u p) i * valueVector X (u q) j =
      valueVector X (u q) i * valueVector X (u p) j) : valueVector X (u p) i = valueVector X (u q) i := by
  have hxpos (k : Fin 3) : 0 < X k := by have h := hx k; omega
  have hNat : startCompleteVertexLabel (X i) L (u p i) * startCompleteVertexLabel (X j) L (u q j) =
      startCompleteVertexLabel (X i) L (u q i) * startCompleteVertexLabel (X j) L (u p j) := by
    rw [valueVector_eq_vertex X (u p) i (hxpos i), valueVector_eq_vertex X (u q) j (hxpos j),
      valueVector_eq_vertex X (u q) i (hxpos i), valueVector_eq_vertex X (u p) j (hxpos j)] at hcross
    exact_mod_cast hcross
  have hu : u p i = u q i := by
    by_contra hne
    exact no_proportional_pairs (X i) (X j) L (hx i) (hx j) hinj hdirect
      (u p i) (u q i) (u p j) (u q j) hne hNat
  simp only [valueVector, offsetVector, hu]

/-- Only the first two windows need regularity; every pair remains direct. -/
theorem projection_rigid {L : ℕ} (X : Fin 3 → ℕ) (u : Fin 3 → Fin 3 → Fin (L + 1))
    (hx : ∀ i, 2 ≤ X i)
    (hrank : ∀ i : Fin 3, i ≠ 2 → Module.finrank F₂ (squareClassSpace (X i) L) = L)
    (hpair : Pairwise (fun i j ↦ Disjoint (squareClassSpace (X i) L) (squareClassSpace (X j) L))) :
    ProjectionRigid (fun p ↦ valueVector X (u p)) := by
  intro i j hij p q hcross
  by_cases hi : i ≠ 2
  · exact projection_value_eq_of_first_injective X u hx i j
      (injective_evenMap_of_rank (X i) L (hrank i hi)) (hpair hij) p q hcross
  · have hi2 : i = 2 := not_ne_iff.mp hi
    have hj : j ≠ 2 := fun h ↦ hij (hi2.trans h.symm)
    have hswap : valueVector X (u p) j * valueVector X (u q) i =
        valueVector X (u q) j * valueVector X (u p) i := by nlinarith [hcross]
    have heq := projection_value_eq_of_first_injective X u hx j i
      (injective_evenMap_of_rank (X j) L (hrank j hj)) (hpair hij.symm) p q hswap
    apply mul_right_cancel₀ (valueVector_pos X hx (u p) j).ne'
    rw [heq]
    simpa only [heq] using hcross

end PaperP1.ThreeWindowRigidity
