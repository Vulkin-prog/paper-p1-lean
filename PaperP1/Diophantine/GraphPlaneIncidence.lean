module

public import PaperP1.Algebra.P3GraphPlaneAffineEvaluation
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Logic.Equiv.Prod

/-! # Exact graph-plane incidence counting for every actual finite set of affine points -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GraphPlaneIncidence

open Finset P3GraphPlaneAffineEvaluation
open scoped Classical

variable {F : Type} [CommRing F]

@[simp] theorem point_zero (a : Fin 3 → F) (u : Fin 2 → F) :
    graphPoint a u 0 = a 0 * u 0 + a 1 * u 1 + a 2 := rfl

@[simp] theorem point_one (a : Fin 3 → F) (u : Fin 2 → F) : graphPoint a u 1 = u 0 := rfl

@[simp] theorem point_two (a : Fin 3 → F) (u : Fin 2 → F) : graphPoint a u 2 = u 1 := rfl

variable [Fintype F]

def slice (S : Finset (Fin 3 → F)) (a : Fin 3 → F) : Finset (Fin 2 → F) :=
  univ.filter (fun u ↦ graphPoint a u ∈ S)

def incidenceEquiv (S : Finset (Fin 3 → F)) :
    (S × (Fin 2 → F)) ≃ {z : (Fin 3 → F) × (Fin 2 → F) // graphPoint z.1 z.2 ∈ S} where
  toFun z :=
    ⟨(![z.2 0, z.2 1, z.1.val 0 - z.2 0 * z.1.val 1 - z.2 1 * z.1.val 2],
      ![z.1.val 1, z.1.val 2]), by
      have he : graphPoint ![z.2 0, z.2 1, z.1.val 0 - z.2 0 * z.1.val 1 - z.2 1 * z.1.val 2]
          ![z.1.val 1, z.1.val 2] = z.1.val := by
        funext i
        fin_cases i <;> simp
      rw [he]
      exact z.1.property⟩
  invFun z := (⟨graphPoint z.val.1 z.val.2, z.property⟩, ![z.val.1 0, z.val.1 1])
  left_inv z := by
    apply Prod.ext
    · apply Subtype.ext
      funext i
      fin_cases i <;> simp
    · funext i
      fin_cases i <;> rfl
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      fin_cases i <;> simp
      ring
    · funext i
      fin_cases i <;> rfl

theorem first_moment (S : Finset (Fin 3 → F)) :
    (∑ a : Fin 3 → F, (slice S a).card) = S.card * Fintype.card F ^ 2 := by
  let p : (Fin 3 → F) → (Fin 2 → F) → Prop := fun a u ↦ graphPoint a u ∈ S
  have hsigma := Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype p)
  have hc := Fintype.card_congr (incidenceEquiv S)
  have hslice (a : Fin 3 → F) : Fintype.card {u : Fin 2 → F // p a u} = (slice S a).card :=
    Fintype.card_of_finset' (p := {u | p a u}) (slice S a) (fun u ↦ by simp [slice, p])
  rw [Fintype.card_sigma] at hsigma
  simp only [Fintype.card_prod, Fintype.card_coe, Fintype.card_fun, Fintype.card_fin] at hc
  rw [hsigma] at hc
  simpa only [hslice] using hc.symm

end PaperP1.GraphPlaneIncidence
