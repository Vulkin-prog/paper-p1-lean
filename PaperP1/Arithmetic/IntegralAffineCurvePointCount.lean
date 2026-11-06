module

public import PaperP1.Arithmetic.UniformIntegralCurveCount
public import Mathlib.Data.Fintype.BigOperators

/-! # The actual affine integer-point set and the full dimension-uniform quadratic degree theorem -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntegralAffineCurvePointCount

universe u

open MvPolynomial CurveIntegerFibres
attribute [local instance] MvPolynomial.gradedAlgebra

def points {F : Type*} [Field F] (n : ℕ) (I : Ideal (MvPolynomial (Fin (n + 1)) F)) (N : ℕ) :
    Finset (Fin n → ℤ) := by
  classical
  exact (Fintype.piFinset (fun _ : Fin n ↦ offsetBox N)).filter (fun w ↦
    ∀ P ∈ I, eval (Fin.cons (1 : F) (fun i ↦ (w i : F))) P = 0)

theorem mem_points {F : Type*} [Field F] (n : ℕ) (I : Ideal (MvPolynomial (Fin (n + 1)) F))
    (N : ℕ) (w : Fin n → ℤ) :
    w ∈ points n I N ↔ (∀ i, |w i| ≤ (N : ℤ)) ∧
      ∀ P ∈ I, eval (Fin.cons (1 : F) (fun i ↦ (w i : F))) P = 0 := by
  classical
  simp only [points, Finset.mem_filter, Fintype.mem_piFinset, mem_offsetBox]

theorem mem_real_points {F : Type*} [Field F] (n : ℕ) (I : Ideal (MvPolynomial (Fin (n + 1)) F))
    (H : ℝ) (hH : 0 ≤ H) (w : Fin n → ℤ) :
    w ∈ points n I ⌊H⌋₊ ↔ (∀ i, |(w i : ℝ)| ≤ H) ∧
      ∀ P ∈ I, eval (Fin.cons (1 : F) (fun i ↦ (w i : F))) P = 0 := by
  rw [mem_points]
  have he (i : Fin n) : |w i| ≤ (⌊H⌋₊ : ℤ) ↔ |(w i : ℝ)| ≤ H :=
    (mem_offsetBox ⌊H⌋₊ (w i)).symm.trans (IntegerGridTheorem.floor_box_iff H hH (w i))
  constructor
  · rintro ⟨hh, hcurve⟩
    exact ⟨fun i ↦ (he i).mp (hh i), hcurve⟩
  · rintro ⟨hh, hcurve⟩
    exact ⟨fun i ↦ (he i).mpr (hh i), hcurve⟩

theorem finite_population {F : Type u} [Field F] [CharZero F] (n : ℕ)
    (I : Ideal (MvPolynomial (Fin (n + 1)) F))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) F)) (hprime : I.IsPrime)
    (d : ℕ) (hd : 0 < d) (b₀ : ℚ)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial
      (HomogeneousQuotientGrading.piece (homogeneousSubmodule (Fin (n + 1)) F) I)
      (Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C b₀))
    (H : ℝ) (hH : 2 < H) (S : Finset (Fin n → ℤ))
    (hcurve : ∀ w ∈ S, ∀ P ∈ I, eval (Fin.cons (1 : F) (fun i ↦ (w i : F))) P = 0)
    (hheight : ∀ w ∈ S, ∀ i, |(w i : ℝ)| ≤ H) :
    (S.card : ℝ) ≤ UniformIntegralCurveCount.realConstant.{u} (n + 1) *
      (d : ℝ) ^ 2 * H ^ (1 / (d : ℝ)) * Real.log H ^ 17 := by
  classical
  let ι : (Fin n → ℤ) → Fin (n + 1) → ℤ := fun w ↦ Fin.cons 1 w
  have hinj : Function.Injective ι := by
    intro w v he
    funext i
    exact congrFun he i.succ
  let T := S.image ι
  have hcard : T.card = S.card := Finset.card_image_of_injective _ hinj
  have hnormalT : ∀ w ∈ T, w 0 = 1 := by
    intro w hw
    obtain ⟨v, _hv, rfl⟩ := Finset.mem_image.mp hw
    rfl
  have hcurveT : ∀ w ∈ T, ∀ P ∈ I, eval (fun i ↦ (w i : F)) P = 0 := by
    intro w hw P hP
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    have he : (fun i ↦ (ι v i : F)) = Fin.cons (1 : F) (fun i ↦ (v i : F)) := by
      funext i
      refine Fin.cases ?_ (fun _ ↦ ?_) i
      · simp [ι]
      · rfl
    rw [he]
    exact hcurve v hv P hP
  have hheightT : ∀ w ∈ T, ∀ i, |(w i : ℝ)| ≤ H := by
    intro w hw i
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · change |((1 : ℤ) : ℝ)| ≤ H
      rw [Int.cast_one, abs_one]
      linarith only [hH]
    · exact hheight v hv j
  have hc := UniformIntegralCurveCount.real_population_bound (n + 1) I hI hprime d hd b₀ hp
    0 H hH T hnormalT hcurveT hheightT
  rwa [hcard] at hc

theorem grid_bound {F : Type u} [Field F] [CharZero F] (n : ℕ)
    (I : Ideal (MvPolynomial (Fin (n + 1)) F))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) F)) (hprime : I.IsPrime)
    (d : ℕ) (hd : 0 < d) (b₀ : ℚ)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial
      (HomogeneousQuotientGrading.piece (homogeneousSubmodule (Fin (n + 1)) F) I)
      (Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C b₀))
    (H : ℝ) (hH : 2 < H) :
    ((points n I ⌊H⌋₊).card : ℝ) ≤ UniformIntegralCurveCount.realConstant.{u} (n + 1) *
      (d : ℝ) ^ 2 * H ^ (1 / (d : ℝ)) * Real.log H ^ 17 := by
  apply finite_population n I hI hprime d hd b₀ hp H hH (points n I ⌊H⌋₊)
  · intro w hw
    exact ((mem_points n I ⌊H⌋₊ w).mp hw).2
  · intro w hw
    exact ((mem_real_points n I H (by linarith) w).mp hw).1

theorem article_13_4 : ∃ κ : ℝ, 0 < κ ∧ ∀ n : ℕ, ∃ c : ℝ, 0 < c ∧
    ∀ (F : Type u) [Field F] [CharZero F], ∀ (I : Ideal (MvPolynomial (Fin (n + 1)) F)),
    I.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) F) → I.IsPrime →
    ∀ (d : ℕ), 0 < d → ∀ (b₀ : ℚ),
    GradedHilbertPolynomial.IsHilbertPolynomial
      (HomogeneousQuotientGrading.piece (homogeneousSubmodule (Fin (n + 1)) F) I)
      (Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C b₀) →
    ∀ (H : ℝ), 2 < H → ((points n I ⌊H⌋₊).card : ℝ) ≤
      c * (d : ℝ) ^ 2 * H ^ (1 / (d : ℝ)) * Real.log H ^ κ := by
  refine ⟨17, by norm_num, fun n ↦ ⟨UniformIntegralCurveCount.realConstant.{u} (n + 1),
    UniformIntegralCurveCount.realConstant_pos (n + 1), ?_⟩⟩
  intro F _hF _hchar I hI hprime d hd b₀ hp H hH
  rw [show (17 : ℝ) = ((17 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  exact grid_bound n I hI hprime d hd b₀ hp H hH

end PaperP1.IntegralAffineCurvePointCount
