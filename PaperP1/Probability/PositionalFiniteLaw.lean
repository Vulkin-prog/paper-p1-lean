module

public import PaperP1.Probability.FiniteConvolutionAlgebra
public import PaperP1.Probability.StoppedFiniteLaw

/-! # Actual finite laws retaining every unsigned position

A configuration is a finitely supported natural-valued function on the
original sites. Its coefficients are the probabilities of the full field,
with arbitrary dependence among the indicators.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalFiniteLaw

open Finset PaperP1.Algebra PaperP1.FiniteConvolutionAlgebra

variable {Ω ι : Type*}

local instance positionalFiniteLawDecidable (P : Prop) : Decidable P := Classical.propDecidable P

abbrev Configuration (ι : Type*) := ι →₀ ℕ

abbrev FieldLaw (ι : Type*) := Law (Configuration ι)

def direction (x : ι) : Configuration ι := Finsupp.single x 1

def delta (x : ι) : FieldLaw ι := atom (direction x) - 1

def configuration (G : Finset ι) (J : ι → Ω → Bool) (ω : Ω) : Configuration ι :=
  ∑ x ∈ G, Finsupp.single x (J x ω).toNat

def difference (I : Finset ι) : FieldLaw ι := ∏ x ∈ I, delta x

def law [Fintype Ω] (G : Finset ι) (w : Ω → ℝ) (J : ι → Ω → Bool) : FieldLaw ι :=
  ∑ ω, scalar (w ω) * atom (configuration G J ω)

theorem configuration_atom_product (G : Finset ι) (J : ι → Ω → Bool) (ω : Ω) :
    (∏ x ∈ G, (1 + delta x * scalar (Probability.indicatorValue (J x ω)))) =
      atom (configuration G J ω) := by
  classical
  rw [configuration, ← atom_sum]
  apply prod_congr rfl
  intro x _
  cases J x ω <;> simp [delta, direction, Probability.indicatorValue, -scalar_apply]

theorem indicator_difference_product (I : Finset ι) (J : ι → Ω → Bool) (ω : Ω) :
    (∏ x ∈ I, delta x * scalar (Probability.indicatorValue (J x ω))) =
      scalar (∏ x ∈ I, (Probability.indicatorValue (J x ω) : ℝ)) * difference I := by
  rw [prod_mul_distrib, ← map_prod]
  exact mul_comm _ _

theorem law_coeff [Fintype Ω] (G : Finset ι) (w : Ω → ℝ) (J : ι → Ω → Bool)
    (v : Configuration ι) :
    (law G w J).coeff v = ∑ ω, if configuration G J ω = v then w ω else 0 := by
  classical
  unfold law
  simp_rw [scalar_mul_atom]
  simp [AddMonoidAlgebra.coeff_sum, Finsupp.single_apply]

theorem law_nonneg [Fintype Ω] (G : Finset ι) (w : Ω → ℝ) (J : ι → Ω → Bool)
    (hw : ∀ ω, 0 ≤ w ω) (v : Configuration ι) : 0 ≤ (law G w J).coeff v := by
  rw [law_coeff]
  exact sum_nonneg fun ω _ ↦ by split_ifs; exact hw ω; exact le_rfl

theorem law_mass [Fintype Ω] (G : Finset ι) (w : Ω → ℝ) (J : ι → Ω → Bool) :
    mass (law G w J) = ∑ ω, w ω := by simp [law, map_sum]

theorem delta_l1Norm (x : ι) : l1Norm (delta x) ≤ 2 := by
  have hh := l1Norm_sub (atom (direction x)) (1 : FieldLaw ι)
  simpa only [delta, l1Norm_atom, l1Norm_one, one_add_one_eq_two] using hh

theorem difference_l1Norm (I : Finset ι) : l1Norm (difference I) ≤ (2 : ℝ) ^ I.card := by
  calc
    _ ≤ ∏ x ∈ I, l1Norm (delta x) := l1Norm_prod I delta
    _ ≤ ∏ _x ∈ I, (2 : ℝ) := prod_le_prod₀ (fun x _ ↦ l1Norm_nonneg (delta x))
      (fun x _ ↦ delta_l1Norm x)
    _ = _ := by simp

def reference [Fintype Ω] (G : Finset ι) (D : Finset ι → Prop)
    (P : Probability.FiniteProbability Ω) (J : ι → Ω → Bool) : FieldLaw ι :=
  ∑ I ∈ retainedSets G D, scalar (Probability.finiteJointMoment P J I) * difference I

def boundaryKernel [Fintype Ω] [LinearOrder ι] (G : Finset ι)
    (P : Probability.FiniteProbability Ω) (J : ι → Ω → Bool) (I : Finset ι) : FieldLaw ι :=
  law (orderedSuffix G I) (fun ω ↦ P.weight ω * ∏ x ∈ I, Probability.indicatorValue (J x ω)) J

theorem boundaryKernel_nonneg [Fintype Ω] [LinearOrder ι] (G : Finset ι)
    (P : Probability.FiniteProbability Ω) (J : ι → Ω → Bool) (I : Finset ι) (v : Configuration ι) :
    0 ≤ (boundaryKernel G P J I).coeff v :=
  law_nonneg _ _ _ (fun ω ↦ mul_nonneg (P.weight_nonneg ω)
    (Probability.indicator_product_nonneg J I ω)) v

theorem boundaryKernel_mass [Fintype Ω] [LinearOrder ι] (G : Finset ι)
    (P : Probability.FiniteProbability Ω) (J : ι → Ω → Bool) (I : Finset ι) :
    mass (boundaryKernel G P J I) = Probability.finiteJointMoment P J I := law_mass _ _ _

theorem boundaryKernel_l1Norm [Fintype Ω] [LinearOrder ι] (G : Finset ι)
    (P : Probability.FiniteProbability Ω) (J : ι → Ω → Bool) (I : Finset ι) :
    l1Norm (boundaryKernel G P J I) = Probability.finiteJointMoment P J I :=
  (l1Norm_eq_mass_of_nonneg _ (boundaryKernel_nonneg G P J I)).trans
    (boundaryKernel_mass G P J I)

theorem pointwise_stopped [LinearOrder ι] (G : Finset ι) (D : Finset ι → Prop)
    (J : ι → Ω → Bool) (ω : Ω) (hD : Hereditary D) (h_empty : D ∅) :
    atom (configuration G J ω) =
      (∑ I ∈ retainedSets G D, scalar (∏ x ∈ I, (Probability.indicatorValue (J x ω) : ℝ)) * difference I) +
      ∑ I ∈ boundarySets G D, difference I *
        (scalar (∏ x ∈ I, (Probability.indicatorValue (J x ω) : ℝ)) *
          atom (configuration (orderedSuffix G I) J ω)) := by
  have hh := stopped_expansion G D (fun x ↦ delta x * scalar (Probability.indicatorValue (J x ω)))
    1 hD h_empty
  simp only [one_mul, one_pow] at hh
  rw [configuration_atom_product] at hh
  simp_rw [indicator_difference_product, configuration_atom_product] at hh
  convert hh using 1
  congr 1
  apply sum_congr rfl
  intro I _
  ring

theorem stopped_identity [Fintype Ω] [LinearOrder ι] (G : Finset ι) (D : Finset ι → Prop)
    (P : Probability.FiniteProbability Ω) (J : ι → Ω → Bool) (hD : Hereditary D) (h_empty : D ∅) :
    law G P.weight J = reference G D P J +
      ∑ I ∈ boundarySets G D, difference I * boundaryKernel G P J I := by
  unfold law
  simp_rw [pointwise_stopped G D J _ hD h_empty, mul_add, mul_sum, sum_add_distrib]
  congr 1
  · rw [sum_comm]
    unfold reference
    apply sum_congr rfl
    intro I _
    unfold Probability.finiteJointMoment finiteExpectation
    rw [map_sum, sum_mul]
    apply sum_congr rfl
    intro ω _
    rw [map_mul]
    ring
  · rw [sum_comm]
    apply sum_congr rfl
    intro I _
    unfold boundaryKernel law
    rw [mul_sum]
    apply sum_congr rfl
    intro ω _
    rw [map_mul]
    ring

theorem stopped_difference [Fintype Ω] [LinearOrder ι] (G : Finset ι) (D : Finset ι → Prop)
    (P : Probability.FiniteProbability Ω) (J : ι → Ω → Bool) (hD : Hereditary D) (h_empty : D ∅) :
    law G P.weight J - reference G D P J =
      ∑ I ∈ boundarySets G D, difference I * boundaryKernel G P J I := by
  rw [stopped_identity G D P J hD h_empty]
  ring

theorem stopped_l1_bound [Fintype Ω] [LinearOrder ι] (G : Finset ι) (D : Finset ι → Prop)
    (P : Probability.FiniteProbability Ω) (J : ι → Ω → Bool) (hD : Hereditary D) (h_empty : D ∅) :
    l1Norm (law G P.weight J - reference G D P J) ≤
      ∑ I ∈ boundarySets G D, (2 : ℝ) ^ I.card * Probability.finiteJointMoment P J I := by
  rw [stopped_difference G D P J hD h_empty]
  apply (l1Norm_sum _ _).trans
  apply sum_le_sum
  intro I _
  have hh := l1Norm_mul (difference I) (boundaryKernel G P J I)
  rw [boundaryKernel_l1Norm] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (difference_l1Norm I)
    (Probability.finiteJointMoment_nonneg P J I))

end PaperP1.PositionalFiniteLaw
