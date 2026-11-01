module

public import PaperP1.Algebra.PrimitiveTripleDirection
public import Mathlib.Data.Rat.Cast.Order

/-! # Primitive parametrization of every integral point of a line -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntegralLine

open PaperP1.PrimitiveTripleDirection

def OnLine (a b v : Fin 3 → ℤ) : Prop :=
  ∀ i j, (b i - a i) * (v j - a j) = (b j - a j) * (v i - a i)

def Collinear {I : Type*} (u : I → Fin 3 → ℤ) : Prop := ∀ a b p, OnLine (u a) (u b) (u p)

theorem collinear_of_rational_parameter {I : Type*} (u : I → Fin 3 → ℤ)
    (a d : Fin 3 → ℚ) (t : I → ℚ) (hu : ∀ p i, (u p i : ℚ) = a i + t p * d i) : Collinear u := by
  intro p q r i j
  have h : (((u q i - u p i) * (u r j - u p j) : ℤ) : ℚ) =
      (((u q j - u p j) * (u r i - u p i) : ℤ) : ℚ) := by
    push_cast
    rw [hu q i, hu p i, hu r j, hu p j, hu q j, hu r i]
    ring
  exact_mod_cast h

theorem exists_primitive_line (a b : Fin 3 → ℤ) (hab : a ≠ b) :
    ∃ d : Fin 3 → ℤ, Primitive d ∧
      (∃ g : ℕ, 0 < g ∧ ∀ i, b i - a i = (g : ℤ) * d i) ∧
      ∀ v : Fin 3 → ℤ, OnLine a b v → ∃ t : ℤ, ∀ i, v i = a i + t * d i := by
  let w : Fin 3 → ℤ := fun i ↦ b i - a i
  have hw : w ≠ 0 := by
    intro h
    apply hab
    funext i
    have hi := congrFun h i
    change b i - a i = 0 at hi
    omega
  obtain ⟨g, hg, d, hd, hfactor⟩ := exists_primitive_direction w hw
  refine ⟨d, hd, ⟨g, hg, hfactor⟩, ?_⟩
  intro v hv
  have hg0 : (g : ℤ) ≠ 0 := by exact_mod_cast (show g ≠ 0 by omega)
  have hcross (i j : Fin 3) : d i * (v j - a j) = d j * (v i - a i) := by
    have h := hv i j
    change w i * (v j - a j) = w j * (v i - a i) at h
    rw [hfactor i, hfactor j] at h
    apply mul_left_cancel₀ hg0
    calc
      _ = (g : ℤ) * d i * (v j - a j) := by ring
      _ = (g : ℤ) * d j * (v i - a i) := h
      _ = _ := by ring
  obtain ⟨t, ht⟩ := integer_multiple_of_minors d (fun i ↦ v i - a i) hd hcross
  exact ⟨t, fun i ↦ by have h := ht i; omega⟩

theorem parametrize_line_of_primitive (a b d : Fin 3 → ℤ) (hd : Primitive d)
    (t : ℤ) (ht0 : t ≠ 0) (hb : ∀ i, b i = a i + t * d i)
    (v : Fin 3 → ℤ) (hv : OnLine a b v) : ∃ s : ℤ, ∀ i, v i = a i + s * d i := by
  have hcross (i j : Fin 3) : d i * (v j - a j) = d j * (v i - a i) := by
    have h := hv i j
    rw [hb i, hb j] at h
    apply mul_left_cancel₀ ht0
    calc
      _ = (a i + t * d i - a i) * (v j - a j) := by ring
      _ = (a j + t * d j - a j) * (v i - a i) := h
      _ = _ := by ring
  obtain ⟨s, hs⟩ := integer_multiple_of_minors d (fun i ↦ v i - a i) hd hcross
  exact ⟨s, fun i ↦ by have h := hs i; omega⟩

end PaperP1.IntegralLine
