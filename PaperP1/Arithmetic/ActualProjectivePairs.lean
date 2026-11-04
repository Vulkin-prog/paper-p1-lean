module

public import PaperP1.Arithmetic.DeterminantPositiveOrientation
public import PaperP1.Diophantine.BiformPointCoordinates

/-! # Literal integer projective pairs and inverse coordinates of the original quadruples -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActualProjectivePairs

open Finset PaperP1.TwoKernelDeterminantBoxes PaperP1.BiformPointCoordinates
open PaperP1.DeterminantPositiveOrientation PaperP1.DeterminantCoordinateFlip

def Primitive (p : Quad) : Prop := p.1.1.Coprime p.1.2 ∧ p.2.1.Coprime p.2.2

def integerPoint (p : Quad) : (Fin 2 → ℤ) × (Fin 2 → ℤ) :=
  (![(p.1.1 : ℤ), p.1.2], ![(p.2.2 : ℤ), p.2.1])

def coordinates (B D : Matrix (Fin 2) (Fin 2) ℤ) (p : Quad) : (Fin 2 → ℤ) × (Fin 2 → ℤ) :=
  move B D (integerPoint p)

theorem integerPoint_injective : Function.Injective integerPoint := by
  intro p q hpq
  have hd : p.1.1 = q.1.1 := by
    have hh : (p.1.1 : ℤ) = q.1.1 := by simpa [integerPoint] using congrArg (fun r ↦ r.1 0) hpq
    exact_mod_cast hh
  have he : p.1.2 = q.1.2 := by
    have hh : (p.1.2 : ℤ) = q.1.2 := by simpa [integerPoint] using congrArg (fun r ↦ r.1 1) hpq
    exact_mod_cast hh
  have hu : p.2.1 = q.2.1 := by
    have hh : (p.2.1 : ℤ) = q.2.1 := by simpa [integerPoint] using congrArg (fun r ↦ r.2 1) hpq
    exact_mod_cast hh
  have hv : p.2.2 = q.2.2 := by
    have hh : (p.2.2 : ℤ) = q.2.2 := by simpa [integerPoint] using congrArg (fun r ↦ r.2 0) hpq
    exact_mod_cast hh
  exact Prod.ext (Prod.ext hd he) (Prod.ext hu hv)

theorem integerPoint_primitive (p : Quad) (hp : Primitive p) :
    ((integerPoint p).1 0).natAbs.Coprime ((integerPoint p).1 1).natAbs ∧
      ((integerPoint p).2 0).natAbs.Coprime ((integerPoint p).2 1).natAbs := by
  exact ⟨by simpa [integerPoint] using hp.1, by simpa [integerPoint] using hp.2.symm⟩

theorem coordinates_injective (A B C D : Matrix (Fin 2) (Fin 2) ℤ)
    (hAB : A * B = 1) (hCD : C * D = 1) : Function.Injective (coordinates B D) :=
  (move_injective B A D C hAB hCD).comp integerPoint_injective

theorem coordinates_card (A B C D : Matrix (Fin 2) (Fin 2) ℤ)
    (hAB : A * B = 1) (hCD : C * D = 1) (S : Finset Quad) :
    (S.image (coordinates B D)).card = S.card := card_image_of_injective S (coordinates_injective A B C D hAB hCD)

theorem coordinates_primitive (A B C D : Matrix (Fin 2) (Fin 2) ℤ)
    (hAB : A * B = 1) (hCD : C * D = 1) (p : Quad) (hp : Primitive p) :
    ((coordinates B D p).1 0).natAbs.Coprime ((coordinates B D p).1 1).natAbs ∧
      ((coordinates B D p).2 0).natAbs.Coprime ((coordinates B D p).2 1).natAbs :=
  move_primitive B A D C hAB hCD (integerPoint p) (integerPoint_primitive p hp)

theorem oriented_primitive (h : ℤ) (S : Finset Quad) (hS : ∀ p ∈ S, Primitive p) :
    ∀ p ∈ orientedPopulation h S, Primitive p := by
  intro p hp
  by_cases hn : h < 0
  · simp only [orientedPopulation, ite_eq_left hn] at hp
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
    have hprim := hS q hq
    exact ⟨hprim.1.symm, hprim.2.symm⟩
  · exact hS p (by simpa only [orientedPopulation, ite_eq_right hn] using hp)

end PaperP1.ActualProjectivePairs
