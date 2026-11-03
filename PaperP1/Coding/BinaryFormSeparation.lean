module

public import PaperP1.Coding.UniqueCoordinateBudget
public import Mathlib.Algebra.Field.ZMod

/-! # Distinct binary coordinate forms can select one coordinate and omit the other -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BinaryFormSeparation

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]

theorem exists_one_zero (f g : U →ₗ[ZMod 2] ZMod 2) (hf : f ≠ 0) (hne : f ≠ g) :
    ∃ x : U, f x = 1 ∧ g x = 0 := by
  classical
  by_contra hnot
  have hbit : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  have hex : ∃ x : U, f x ≠ 0 := by
    by_contra! h
    apply hf
    ext x
    exact h x
  obtain ⟨v, hv⟩ := hex
  have hfv : f v = 1 := (hbit _).resolve_left hv
  have hg (x : U) (hx : f x = 1) : g x = 1 :=
    (hbit _).resolve_left (fun hz ↦ hnot ⟨x, hx, hz⟩)
  apply hne
  ext x
  rcases hbit (f x) with hx | hx
  · have hsum : g (x + v) = 1 := hg (x + v) (by rw [map_add, hx, hfv, zero_add])
    rw [map_add, hg v hfv] at hsum
    have hzero : g x = 0 := add_right_cancel (hsum.trans (zero_add (1 : ZMod 2)).symm)
    exact hx.trans hzero.symm
  · exact hx.trans (hg x hx).symm

theorem good_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Submodule (ZMod 2) (ι → ZMod 2)) (i j : ι)
    (hi : i ∈ UniqueCoordinateBudget.good R) (hne : i ≠ j) :
    ∃ w : R, w.val i = 1 ∧ w.val j = 0 := by
  obtain ⟨hi0, huniq⟩ := (UniqueCoordinateBudget.mem_good R i).mp hi
  apply exists_one_zero (UniqueCoordinateBudget.form R i) (UniqueCoordinateBudget.form R j) hi0
  intro heq
  exact hne (huniq j heq.symm).symm

end PaperP1.BinaryFormSeparation
