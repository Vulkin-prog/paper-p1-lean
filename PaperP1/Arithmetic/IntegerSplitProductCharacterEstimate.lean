module

public import PaperP1.Arithmetic.SplitProductCharacterEstimate
public import PaperP1.Arithmetic.SplitRadicalFiniteFieldPointCount

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.IntegerSplitProductCharacterEstimate
open Finset Polynomial
open PaperP1.SplitProductInversion PaperP1.SplitRadicalFiniteFieldPointCount
open scoped Classical

theorem linear_image_eval {F : Type*} [Field F] (S : Finset ℤ)
    (hinj : Set.InjOn (Int.cast : ℤ → F) (S : Set ℤ)) (x : F) :
    (linearProduct (S.image (Int.cast : ℤ → F))).eval x = linearValue F S x := by
  simp only [linearProduct, linearValue, eval_prod, eval_add, eval_X, eval_C]
  exact prod_image hinj

theorem uniform_absolute (D : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ K : ℕ, ∀ (p : ℕ) (hp : p.Prime), K ≤ p →
      letI : Fact p.Prime := ⟨hp⟩
      ∀ S : Finset ℤ, S.Nonempty → S.card ≤ D →
        Set.InjOn (Int.cast : ℤ → ZMod p) (S : Set ℤ) →
        |((∑ x : ZMod p, quadraticChar (ZMod p) (linearValue (ZMod p) S x) : ℤ) : ℝ)| ≤ η * p := by
  obtain ⟨K, hK⟩ := PaperP1.SplitProductCharacterEstimate.uniform_absolute D η hη
  refine ⟨K, ?_⟩
  intro p hp hlarge
  let : Fact p.Prime := ⟨hp⟩
  intro S hS hD hinj
  have hnon : (S.image (Int.cast : ℤ → ZMod p)).Nonempty := hS.image _
  have hcard : (S.image (Int.cast : ℤ → ZMod p)).card ≤ D := by
    rw [card_image_of_injOn hinj]
    exact hD
  have hb := hK p hp hlarge (S.image (Int.cast : ℤ → ZMod p)) hnon hcard
  have he (x : ZMod p) := linear_image_eval S hinj x
  have hdec : (fun a b : ZMod p ↦ Classical.propDecidable (a = b)) = ZMod.decidableEq p :=
    Subsingleton.elim _ _
  rw [hdec] at he
  simp_rw [he] at hb
  exact hb

end PaperP1.IntegerSplitProductCharacterEstimate
