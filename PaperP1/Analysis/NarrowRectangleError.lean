module

public import PaperP1.Analysis.RelativeRamareRemainder
public import PaperP1.Analysis.NarrowBoundaryMeanValue
public import PaperP1.Analysis.NarrowRamareRectangle
public import PaperP1.Analysis.NarrowRectangleDifference
public import PaperP1.Analysis.NarrowRectangleWeight

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.NarrowRectangleError
open Finset PaperP1 MeasureTheory
open scoped Classical

theorem quantitative_bound (X H : ℕ) (hX : 0 < X) (hH : 2 ≤ H)
    (P Q : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (hPQ : Disjoint P Q)
    (f : ℕ → ℂ) (hf : ∀ a b, f (a*b)=f a*f b) (hb : ∀ n ∈ Ico X (4*X), ‖f n‖ ≤ 1)
    (T : ℝ) (hT : 0 < T) (hTX : T ≤ X) :
    (∫ t in -T..T, ‖NarrowRamareRectangle.rectangle X H P Q f t-
      RelativeRamareRemainder.quotient X P Q f t‖^2) ≤
        NarrowBoundaryMeanValue.constant*(6/(H : ℝ)+2/(X : ℝ)) := by
  have hh := NarrowBoundaryMeanValue.supported_uniform_bound X hX (Ico X (4*X))
    (NarrowRectangleWeight.boundary X H) (fun _n hn ↦ hn) (filter_subset _ _)
    (NarrowRectangleDifference.coefficient X H P Q f)
    (fun n hn ↦ NarrowRectangleDifference.coefficient_norm_bound X H P Q hP f n (hb n hn))
    (fun n hn hnot ↦ NarrowRectangleDifference.coefficient_zero X H hX hH P Q hP f n hn hnot) T hT hTX
  simp_rw [NarrowRectangleDifference.difference_identity X H hX hH P Q hP hQ hPQ f hf]
  exact hh.trans (mul_le_mul_of_nonneg_left (NarrowBoundaryMeanValue.boundary_card_normalized X H hX hH)
    NarrowBoundaryMeanValue.constant_pos.le)

theorem small_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ H₀ : ℕ, 2 ≤ H₀ ∧ ∃ X₀ : ℕ, 1 ≤ X₀ ∧ ∀ H ≥ H₀, ∀ X ≥ X₀,
      ∀ P Q : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ q ∈ Q, q.Prime) → Disjoint P Q →
      ∀ f : ℕ → ℂ, (∀ a b, f (a*b)=f a*f b) → (∀ n ∈ Ico X (4*X), ‖f n‖ ≤ 1) →
      ∀ T : ℝ, 0 < T → T ≤ X →
      (∫ t in -T..T, ‖NarrowRamareRectangle.rectangle X H P Q f t-
        RelativeRamareRemainder.quotient X P Q f t‖^2) ≤ ε := by
  let C := NarrowBoundaryMeanValue.constant
  let H₀ := ⌈12*C/ε⌉₊+2
  let X₀ := ⌈4*C/ε⌉₊+1
  refine ⟨H₀,by dsimp only [H₀]; omega,X₀,by dsimp only [X₀]; omega,?_⟩
  intro H hH X hX P Q hP hQ hPQ f hf hb T hT hTX
  have hHp : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by dsimp only [H₀] at hH; omega)
  have hXp : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by dsimp only [X₀] at hX; omega)
  have hHlarge : 12*C/ε ≤ (H : ℝ) := by
    have hh : ⌈12*C/ε⌉₊ ≤ H := by dsimp only [H₀] at hH; omega
    exact (Nat.le_ceil _).trans (by exact_mod_cast hh)
  have hXlarge : 4*C/ε ≤ (X : ℝ) := by
    have hh : ⌈4*C/ε⌉₊ ≤ X := by dsimp only [X₀] at hX; omega
    exact (Nat.le_ceil _).trans (by exact_mod_cast hh)
  have hHmul := (div_le_iff₀ hε).mp hHlarge
  have hXmul := (div_le_iff₀ hε).mp hXlarge
  have h1 : C*(6/(H : ℝ)) ≤ ε/2 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hHp).mpr
    nlinarith only [hHmul]
  have h2 : C*(2/(X : ℝ)) ≤ ε/2 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hXp).mpr
    nlinarith only [hXmul]
  have hs : C*(6/(H : ℝ)+2/(X : ℝ)) ≤ ε := by nlinarith only [h1,h2]
  exact (quantitative_bound X H (by exact_mod_cast hXp) (by dsimp only [H₀] at hH; omega)
    P Q hP hQ hPQ f hf hb T hT hTX).trans hs
end PaperP1.NarrowRectangleError
