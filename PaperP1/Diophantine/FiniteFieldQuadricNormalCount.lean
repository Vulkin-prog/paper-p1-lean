module

public import PaperP1.Algebra.QuadraticDirectionFibres
public import PaperP1.Algebra.LinearPolynomialSubstitutionDegree
public import PaperP1.Diophantine.FiniteFieldPlaneZeroBound

/-! # A leading-coefficient-one count for the actual smooth-origin quadratic normal form -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteFieldQuadricNormalCount

open MvPolynomial Finset
open scoped Classical

variable {F : Type*} [Field F]

def boundary : MvPolynomial (Fin 3) F →+* MvPolynomial (Fin 2) F :=
  eval₂Hom C (Fin.cons 0 X)

theorem boundary_evaluation (Q : MvPolynomial (Fin 3) F) (u : Fin 2 → F) :
    eval u (boundary Q) = eval (Fin.cons 0 u) Q := by
  have he : (eval u).comp (boundary (F := F)) = eval (Fin.cons 0 u) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [boundary]
    · intro i
      cases i using Fin.cases <;> simp [boundary]
  exact RingHom.congr_fun he Q

theorem boundary_degree (Q : MvPolynomial (Fin 3) F) (hQ : Q.IsHomogeneous 2) :
    (boundary Q).totalDegree ≤ 2 := by
  have hY : ∀ i : Fin 3, ((Fin.cons 0 X : Fin 3 → MvPolynomial (Fin 2) F) i).totalDegree ≤ 1 := by
    intro i
    cases i using Fin.cases <;> simp
  have hh := LinearPolynomialSubstitutionDegree.substitution_bound
    (RingHom.id F) (Fin.cons 0 X) hY Q
  have hh' : (boundary Q).totalDegree ≤ Q.totalDegree := by
    simpa only [boundary, RingHom.comp_id] using hh
  exact hh'.trans hQ.totalDegree_le

theorem cardinality_bound [Fintype F] [DecidableEq F]
    (a : F) (ha : a ≠ 0) (Q : MvPolynomial (Fin 3) F) (hQ : Q.IsHomogeneous 2)
    (hb : boundary Q ≠ 0) (S : Finset (Fin 3 → F))
    (hS : ∀ v ∈ S, a * v 0 + eval v Q = 0) :
    S.card ≤ Fintype.card F ^ 2 + 2 * Fintype.card F := by
  let U := S.filter (fun v ↦ v 0 ≠ 0)
  let T := S.filter (fun v ↦ v 0 = 0)
  have hU : U.card ≤ Fintype.card F ^ 2 := by
    calc
      _ ≤ (univ : Finset (Fin 2 → F)).card :=
        card_le_card_of_injOn QuadraticDirectionFibres.direction
          (fun _ _ ↦ mem_univ _) (by
            intro v hv w hw he
            exact QuadraticDirectionFibres.injective_on_roots a ha Q hQ v w
              (mem_filter.mp hv).2 (mem_filter.mp hw).2
              (hS v (mem_filter.mp hv).1) (hS w (mem_filter.mp hw).1) he)
      _ = _ := by simp
  let Z := T.image (fun v ↦ Fin.tail v)
  have hinj : (↑T : Set (Fin 3 → F)).InjOn (fun v ↦ Fin.tail v) := by
    intro v hv w hw he
    have hv0 := (mem_filter.mp hv).2
    have hw0 := (mem_filter.mp hw).2
    funext i
    cases i using Fin.cases with
    | zero => exact hv0.trans hw0.symm
    | succ i => exact congrFun he i
  have hcard : Z.card = T.card := card_image_of_injOn hinj
  have hz : ∀ u ∈ Z, eval u (boundary Q) = 0 := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hu
    have hv0 := (mem_filter.mp hv).2
    have hroot := hS v (mem_filter.mp hv).1
    have he : Fin.cons 0 (Fin.tail v) = v := by
      funext i
      cases i using Fin.cases with
      | zero => simpa only [Fin.cons_zero] using hv0.symm
      | succ i => rfl
    rw [boundary_evaluation, he]
    simpa only [hv0, mul_zero, zero_add] using hroot
  have hT : T.card ≤ 2 * Fintype.card F := by
    have hh := FiniteFieldPlaneZeroBound.multivariate_card (boundary Q) hb Z hz
    rw [hcard] at hh
    exact hh.trans (Nat.mul_le_mul_right _ (boundary_degree Q hQ))
  have hsplit : U.card + T.card = S.card := by
    simpa only [U, T, ne_eq, not_not] using
      card_filter_add_card_filter_not (s := S) (fun v ↦ v 0 ≠ 0)
  rw [← hsplit]
  exact Nat.add_le_add hU hT

end PaperP1.FiniteFieldQuadricNormalCount
