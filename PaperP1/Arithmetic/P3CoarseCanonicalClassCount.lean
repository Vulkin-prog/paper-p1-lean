module

public import PaperP1.Arithmetic.P3CanonicalSmoothResidues
public import PaperP1.Algebra.IntegerPolynomialReduction
public import PaperP1.Algebra.LinearPolynomialSubstitutionDegree
public import PaperP1.Diophantine.FiniteFieldSurfaceZeroBound
public import Mathlib.Algebra.Field.ZMod

/-! # The actual canonical smooth surface classes satisfy a proved coefficient-uniform coarse bound -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3CoarseCanonicalClassCount

open MvPolynomial Finset P3CanonicalSmoothResidues
open scoped Classical

def fieldCoordinates {p : ℕ} (r : Fin 3 → Fin p) : Fin 3 → ZMod p := fun k ↦ (r k).val

theorem fieldCoordinates_injective (p : ℕ) : Function.Injective (fieldCoordinates (p := p)) := by
  intro r s he
  funext k
  apply Fin.ext
  have hk := congrArg (fun v : Fin 3 → ZMod p ↦ (v k).val) he
  simpa only [fieldCoordinates, ZMod.val_natCast_of_lt (r k).isLt,
    ZMod.val_natCast_of_lt (s k).isLt] using hk

theorem reduced_evaluation (p : ℕ) (P : MvPolynomial (Fin 4) ℤ) (r : Fin 3 → Fin p) :
    eval (fieldCoordinates r) (map (Int.castRingHom (ZMod p)) (LastChartPolynomial.dehomogenize P)) =
      ((eval (representative r) P : ℤ) : ZMod p) := by
  have hh := IntegerPolynomialReduction.map_evaluation (Int.castRingHom (ZMod p))
    (fun k : Fin 3 ↦ ((r k).val : ℤ)) (LastChartPolynomial.dehomogenize P)
  change ((eval (fun k : Fin 3 ↦ ((r k).val : ℤ)) (LastChartPolynomial.dehomogenize P) : ℤ) : ZMod p) =
    eval (fun k : Fin 3 ↦ (((r k).val : ℤ) : ZMod p))
      (map (Int.castRingHom (ZMod p)) (LastChartPolynomial.dehomogenize P)) at hh
  have hc : (fun k : Fin 3 ↦ (((r k).val : ℤ) : ZMod p)) = fieldCoordinates r := by
    funext k
    change (((r k).val : ℤ) : ZMod p) = ((r k).val : ZMod p)
    simp only [Int.cast_natCast]
  rw [hc, LastChartPolynomial.evaluation] at hh
  exact hh.symm

theorem affine_zero (p : ℕ) (P : MvPolynomial (Fin 4) ℤ) (c : Class p P) :
    eval (fieldCoordinates c.val)
      (map (Int.castRingHom (ZMod p)) (LastChartPolynomial.dehomogenize P)) = 0 := by
  rw [reduced_evaluation]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr c.property.1

theorem reduced_degree_le (p d : ℕ) (hp : p.Prime) (P : MvPolynomial (Fin 4) ℤ)
    (hhom : P.IsHomogeneous d) :
    (map (Int.castRingHom (ZMod p)) (LastChartPolynomial.dehomogenize P)).totalDegree ≤ d := by
  let : Fact p.Prime := ⟨hp⟩
  rw [IntegerPolynomialReduction.map_dehomogenize]
  apply (LinearPolynomialSubstitutionDegree.substitution_bound (Int.castRingHom (ZMod p))
    (Fin.snoc X 1) ?_ P).trans hhom.totalDegree_le
  intro k
  cases k using Fin.lastCases with
  | last =>
    change (1 : MvPolynomial (Fin 3) (ZMod p)).totalDegree ≤ 1
    simp
  | cast k => simp

theorem card_le_of_reduced_nonzero (p d : ℕ) (hp : p.Prime) (P : MvPolynomial (Fin 4) ℤ)
    (hhom : P.IsHomogeneous d)
    (hP : map (Int.castRingHom (ZMod p)) (LastChartPolynomial.dehomogenize P) ≠ 0) :
    Fintype.card (Class p P) ≤ d * p ^ 2 := by
  let : Fact p.Prime := ⟨hp⟩
  let S := (univ : Finset (Class p P)).image (fun c ↦ fieldCoordinates c.val)
  have hi : Function.Injective (fun c : Class p P ↦ fieldCoordinates c.val) :=
    (fieldCoordinates_injective p).comp Subtype.val_injective
  have hs : S.card = Fintype.card (Class p P) := by
    dsimp only [S]
    rw [Finset.card_image_of_injective _ hi, card_univ]
  have hroots : ∀ z ∈ S,
      eval z (map (Int.castRingHom (ZMod p)) (LastChartPolynomial.dehomogenize P)) = 0 := by
    intro z hz
    obtain ⟨c, _, rfl⟩ := mem_image.mp hz
    exact affine_zero p P c
  have hb := FiniteFieldSurfaceZeroBound.multivariate_card
    (map (Int.castRingHom (ZMod p)) (LastChartPolynomial.dehomogenize P)) hP S hroots
  rw [hs, ZMod.card] at hb
  exact hb.trans (Nat.mul_le_mul_right _ (reduced_degree_le p d hp P hhom))

theorem classes_empty_of_reduced_zero (p d : ℕ) (P : MvPolynomial (Fin 4) ℤ)
    (hhom : P.IsHomogeneous d)
    (hP : map (Int.castRingHom (ZMod p)) (LastChartPolynomial.dehomogenize P) = 0) :
    IsEmpty (Class p P) := by
  refine ⟨fun c ↦ ?_⟩
  obtain ⟨k, hk⟩ := NormalizedP3SurfaceDeterminant.free_partial p d P hhom
    (representative c.val) (representative_last c.val) c.property.1 c.property.2
  have hz : eval (fieldCoordinates c.val)
      (map (Int.castRingHom (ZMod p)) (pderiv k (LastChartPolynomial.dehomogenize P))) = 0 := by
    rw [← pderiv_map, hP]
    simp
  have hcast : ((eval (representative c.val) (pderiv k.castSucc P) : ℤ) : ZMod p) = 0 := by
    calc
      _ = eval (fieldCoordinates c.val)
          (map (Int.castRingHom (ZMod p)) (pderiv k (LastChartPolynomial.dehomogenize P))) := by
        rw [LastChartPolynomial.pderiv]
        exact (reduced_evaluation p (pderiv k.castSucc P) c.val).symm
      _ = 0 := hz
  exact hk ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hcast)

theorem cardinality_bound (p d : ℕ) (hp : p.Prime) (P : MvPolynomial (Fin 4) ℤ)
    (hhom : P.IsHomogeneous d) : Fintype.card (Class p P) ≤ d * p ^ 2 := by
  by_cases hP : map (Int.castRingHom (ZMod p)) (LastChartPolynomial.dehomogenize P) = 0
  · let : IsEmpty (Class p P) := classes_empty_of_reduced_zero p d P hhom hP
    simp
  · exact card_le_of_reduced_nonzero p d hp P hhom hP

end PaperP1.P3CoarseCanonicalClassCount
