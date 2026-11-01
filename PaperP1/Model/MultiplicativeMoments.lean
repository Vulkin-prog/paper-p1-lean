module

public import PaperP1.Model.ParityCharacters
public import PaperP1.Affine.Characters
public import PaperP1.Probability.CylinderExpectations

/-! # Actual even moments as counts of square-product tuples -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.Model.MultiplicativeMoments

open Finset MeasureTheory PaperP1.Arithmetic PaperP1.Model PaperP1.Algebra PaperP1.Affine
open PaperP1.Model.InfiniteRademacher PaperP1.Probability.CylinderExpectations
open PaperP1.Probability.InfiniteCylinderTransfer

local instance : MeasurableSpace F₂ := ⊤

theorem finite_value_mean (M n : ℕ) (hn : n ≠ 0) (hbounded : parityVec n ∈ boundedPrimeParity M) :
    finiteExpectation (cylinderProbability M).weight
      (fun ω ↦ (randomMultiplicativeValue ω n : ℝ)) = if IsSquare n then 1 else 0 := by
  have hzero : valueLinear M n = 0 ↔ IsSquare n := by
    rw [← parityPairing_parityVec,
      parityPairing_eq_zero_iff_of_bounded M (parityVec n) hbounded,
      parityVec_eq_zero_iff_isSquare hn]
  change finiteExpectation (PaperP1.Probability.uniformFiniteProbability (SampleSpace M)).weight
    (realCharacter (valueLinear M n)) = _
  rw [uniform_character_expectation, hzero]
  split_ifs <;> rfl

theorem value_prod {ι : Type*} (I : Finset ι) (X : ι → ℕ) (hX : ∀ i ∈ I, X i ≠ 0)
    {M : ℕ} (ω : SampleSpace M) :
    randomMultiplicativeValue ω (∏ i ∈ I, X i) = ∏ i ∈ I, randomMultiplicativeValue ω (X i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [randomMultiplicativeValue, valueBit, phase]
  | @insert i I hi ih =>
    have hXi := hX i (mem_insert_self i I)
    have hXI : ∀ j ∈ I, X j ≠ 0 := fun j hj ↦ hX j (mem_insert_of_mem hj)
    rw [prod_insert hi, prod_insert hi,
      randomMultiplicativeValue_mul ω hXi (prod_ne_zero_iff.mpr hXI), ih hXI]

theorem bounded_product_parity {ι : Type*} (M : ℕ) (I : Finset ι) (X : ι → ℕ)
    (hX : ∀ i ∈ I, X i ≠ 0) (hcut : ∀ i ∈ I, X i ≤ M) :
    parityVec (∏ i ∈ I, X i) ∈ boundedPrimeParity M := by
  rw [parityVec_prod I X hX]
  exact Submodule.sum_mem _ fun i hi ↦ parityVec_mem_boundedPrimeParity (hcut i hi)

theorem finite_product_mean {ι : Type*} (M : ℕ) (I : Finset ι) (X : ι → ℕ)
    (hX : ∀ i ∈ I, X i ≠ 0) (hcut : ∀ i ∈ I, X i ≤ M) :
    finiteExpectation (cylinderProbability M).weight
      (fun ω ↦ ∏ i ∈ I, (randomMultiplicativeValue ω (X i) : ℝ)) =
      if IsSquare (∏ i ∈ I, X i) then 1 else 0 := by
  have hv : (fun ω : SampleSpace M ↦ ∏ i ∈ I, (randomMultiplicativeValue ω (X i) : ℝ)) =
      (fun ω ↦ (randomMultiplicativeValue ω (∏ i ∈ I, X i) : ℝ)) := by
    funext ω
    rw [← Int.cast_prod, ← value_prod I X hX ω]
  rw [hv]
  exact finite_value_mean M _ (prod_ne_zero_iff.mpr hX) (bounded_product_parity M I X hX hcut)

def squareTuples {ι : Type*} [Fintype ι] (X : ι → ℕ) (v : ℕ) : Finset (Fin v → ι) := by
  classical
  exact univ.filter fun n ↦ IsSquare (∏ i, X (n i))

theorem finite_even_moment {ι : Type*} [Fintype ι] (M : ℕ) (X : ι → ℕ)
    (hX : ∀ i, X i ≠ 0) (hcut : ∀ i, X i ≤ M) (v : ℕ) (hv : Even v) :
    finiteExpectation (cylinderProbability M).weight
      (fun ω ↦ |∑ i, (randomMultiplicativeValue ω (X i) : ℝ)| ^ v) =
      ((squareTuples X v).card : ℝ) := by
  classical
  calc
    _ = finiteExpectation (cylinderProbability M).weight
        (fun ω ↦ (∑ i, (randomMultiplicativeValue ω (X i) : ℝ)) ^ v) := by
      congr 1
      funext ω
      exact hv.pow_abs _
    _ = finiteExpectation (cylinderProbability M).weight
        (fun ω ↦ ∑ n : Fin v → ι, ∏ i, (randomMultiplicativeValue ω (X (n i)) : ℝ)) := by
      congr 1
      funext ω
      exact Fintype.sum_pow _ v
    _ = ∑ n : Fin v → ι, finiteExpectation (cylinderProbability M).weight
        (fun ω ↦ ∏ i, (randomMultiplicativeValue ω (X (n i)) : ℝ)) :=
      finiteExpectation_sum _ univ _
    _ = ∑ n : Fin v → ι, if IsSquare (∏ i, X (n i)) then 1 else 0 := by
      apply sum_congr rfl
      intro n _
      exact finite_product_mean M univ (fun i ↦ X (n i))
        (fun i _ ↦ hX (n i)) (fun i _ ↦ hcut (n i))
    _ = _ := by simp [squareTuples]

theorem infinite_even_moment {ι : Type*} [Fintype ι] (X : ι → ℕ)
    (hX : ∀ i, X i ≠ 0) (v : ℕ) (hv : Even v) :
    (∫ ω, |∑ i, (infiniteRandomValue ω (X i) : ℝ)| ^ v ∂infiniteRademacherMeasure) =
      ((squareTuples X v).card : ℝ) := by
  classical
  let M := (univ : Finset ι).sup X
  have hcut : ∀ i, X i ≤ M := fun i ↦ le_sup (mem_univ i)
  have hobs : (fun ω ↦ |∑ i, (infiniteRandomValue ω (X i) : ℝ)| ^ v) =
      (fun ω ↦ |∑ i, (randomMultiplicativeValue (restrictToFinite M ω) (X i) : ℝ)| ^ v) := by
    funext ω
    congr 2
    apply sum_congr rfl
    intro i _
    rw [randomMultiplicativeValue_restrictToFinite_eq_infiniteRandomValue ω (hcut i)]
  rw [hobs, infiniteCylinder_integral M
    (fun σ ↦ |∑ i, (randomMultiplicativeValue σ (X i) : ℝ)| ^ v)]
  exact finite_even_moment M X hX hcut v hv

end PaperP1.Model.MultiplicativeMoments
