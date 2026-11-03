module

public import PaperP1.Probability.L1Norm

/-! # Finite signed convolution laws on an arbitrary commutative additive monoid

The same ordinary mass and ℓ¹ estimates hold for full configurations and
for scalar counts. No topology or choice of an integer encoding is needed.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteConvolutionAlgebra

open Finset

variable {M : Type*} [AddCommMonoid M]

abbrev Law (M : Type*) [AddCommMonoid M] := AddMonoidAlgebra ℝ M

def scalar : ℝ →+* Law M := AddMonoidAlgebra.singleZeroRingHom

def atom (m : M) : Law M := AddMonoidAlgebra.single m 1

def mass : Law M →+* ℝ :=
  AddMonoidAlgebra.liftNCRingHom (RingHom.id ℝ)
    (1 : Multiplicative M →* ℝ) (fun _ _ ↦ Commute.all _ _)

def l1Norm (ν : Law M) : ℝ := ν.coeff.sum fun _ r ↦ |r|

@[simp] theorem scalar_apply (r : ℝ) : (scalar r : Law M) = AddMonoidAlgebra.single 0 r := rfl

@[simp] theorem atom_zero : (atom 0 : Law M) = 1 := rfl

theorem scalar_mul_atom (r : ℝ) (m : M) :
    (scalar r : Law M) * atom m = AddMonoidAlgebra.single m r := by
  simp [scalar_apply, atom]

theorem atom_sum {ι : Type*} (G : Finset ι) (f : ι → M) :
    (∏ i ∈ G, atom (f i) : Law M) = atom (∑ i ∈ G, f i) := by
  simp [atom, AddMonoidAlgebra.prod_single]

@[simp] theorem mass_single (m : M) (r : ℝ) :
    mass (AddMonoidAlgebra.single m r) = r := by simp [mass]

theorem mass_eq_sum_coeff (ν : Law M) : mass ν = ν.coeff.sum (fun _ r ↦ r) := by
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single ν]
  simp only [Finsupp.sum, map_sum, mass_single]

@[simp] theorem mass_atom (m : M) : mass (atom m) = 1 := by simp [atom]

@[simp] theorem mass_scalar (r : ℝ) : mass (scalar r : Law M) = r := by simp

theorem l1Norm_nonneg (ν : Law M) : 0 ≤ l1Norm ν := by
  unfold l1Norm Finsupp.sum
  exact sum_nonneg fun _ _ ↦ abs_nonneg _

@[simp] theorem l1Norm_zero : l1Norm (0 : Law M) = 0 := by simp [l1Norm]

theorem l1Norm_single (m : M) (r : ℝ) :
    l1Norm (AddMonoidAlgebra.single m r) = |r| := by
  unfold l1Norm
  rw [AddMonoidAlgebra.coeff_single, Finsupp.sum_single_index]
  simp

@[simp] theorem l1Norm_atom (m : M) : l1Norm (atom m) = 1 := by
  simpa [atom] using l1Norm_single m 1

@[simp] theorem l1Norm_one : l1Norm (1 : Law M) = 1 := l1Norm_atom 0

@[simp] theorem l1Norm_scalar (r : ℝ) : l1Norm (scalar r : Law M) = |r| :=
  l1Norm_single 0 r

theorem l1Norm_eq_sum_of_support_subset (ν : Law M) (s : Finset M)
    (hs : ν.coeff.support ⊆ s) : l1Norm ν = ∑ m ∈ s, |ν.coeff m| :=
  Finsupp.sum_of_support_subset _ hs _ (fun _ _ ↦ abs_zero)

theorem l1Norm_add (μ ν : Law M) : l1Norm (μ + ν) ≤ l1Norm μ + l1Norm ν := by
  classical
  let s := μ.coeff.support ∪ ν.coeff.support
  have hμ : μ.coeff.support ⊆ s := subset_union_left
  have hν : ν.coeff.support ⊆ s := subset_union_right
  have hsum : (μ + ν).coeff.support ⊆ s := by
    rw [AddMonoidAlgebra.coeff_add]
    exact Finsupp.support_add
  rw [l1Norm_eq_sum_of_support_subset (μ + ν) s hsum,
    l1Norm_eq_sum_of_support_subset μ s hμ, l1Norm_eq_sum_of_support_subset ν s hν,
    ← sum_add_distrib]
  exact sum_le_sum fun _ _ ↦ abs_add_le _ _

@[simp] theorem l1Norm_neg (ν : Law M) : l1Norm (-ν) = l1Norm ν := by
  simp [l1Norm, AddMonoidAlgebra.coeff_neg, Finsupp.sum]

theorem l1Norm_sub (μ ν : Law M) : l1Norm (μ - ν) ≤ l1Norm μ + l1Norm ν := by
  simpa only [sub_eq_add_neg, l1Norm_neg] using l1Norm_add μ (-ν)

theorem l1Norm_sum {ι : Type*} (s : Finset ι) (f : ι → Law M) :
    l1Norm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, l1Norm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [sum_insert hi, sum_insert hi]
    exact (l1Norm_add _ _).trans (add_le_add_right ih _)

theorem l1Norm_mul (μ ν : Law M) : l1Norm (μ * ν) ≤ l1Norm μ * l1Norm ν := by
  classical
  rw [AddMonoidAlgebra.mul_def]
  change l1Norm (∑ i ∈ μ.coeff.support,
    ∑ j ∈ ν.coeff.support, AddMonoidAlgebra.single (i + j) (μ.coeff i * ν.coeff j)) ≤ _
  calc
    _ ≤ ∑ i ∈ μ.coeff.support,
        l1Norm (∑ j ∈ ν.coeff.support, AddMonoidAlgebra.single (i + j) (μ.coeff i * ν.coeff j)) := l1Norm_sum _ _
    _ ≤ ∑ i ∈ μ.coeff.support, ∑ j ∈ ν.coeff.support, |μ.coeff i * ν.coeff j| := by
      apply sum_le_sum
      intro i _
      simpa only [l1Norm_single] using l1Norm_sum ν.coeff.support
        (fun j ↦ AddMonoidAlgebra.single (i + j) (μ.coeff i * ν.coeff j))
    _ = l1Norm μ * l1Norm ν := by
      simp only [abs_mul, l1Norm, Finsupp.sum, mul_sum, sum_mul]
      exact sum_comm

theorem l1Norm_prod {ι : Type*} (s : Finset ι) (f : ι → Law M) :
    l1Norm (∏ i ∈ s, f i) ≤ ∏ i ∈ s, l1Norm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [prod_insert hi, prod_insert hi]
    exact (l1Norm_mul _ _).trans (mul_le_mul_of_nonneg_left ih (l1Norm_nonneg _))

theorem l1Norm_eq_mass_of_nonneg (ν : Law M) (hν : ∀ m, 0 ≤ ν.coeff m) :
    l1Norm ν = mass ν := by
  rw [mass_eq_sum_coeff]
  unfold l1Norm Finsupp.sum
  exact sum_congr rfl fun m _ ↦ abs_of_nonneg (hν m)

end PaperP1.FiniteConvolutionAlgebra
