module

public import PaperP1.Probability.FiniteCoupling

/-! # Exact source deletion and the size-weighted count law

The identities hold for arbitrary real weights. No independence or common
marginal is used, and the active weighted law is not divided by its mass.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IndicatorDeletion

open PaperP1.Algebra PaperP1.Probability Finset

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq ι]

def activeLaw (G : Finset ι) (w : Ω → ℝ) (J : ι → Ω → Bool) (x : ι) : SignedLaw ℝ :=
  countLaw (G.erase x) (fun ω ↦ w ω * indicatorValue (J x ω)) J

def sizeWeightedLaw (G : Finset ι) (w : Ω → ℝ) (J : ι → Ω → Bool) : SignedLaw ℝ :=
  ∑ ω, scalar (w ω * (indicatorCount G J ω : ℝ)) * atom (indicatorCount G J ω)

omit [Fintype Ω] in
theorem count_erase_add {G : Finset ι} {x : ι} (hx : x ∈ G)
    (J : ι → Ω → Bool) (ω : Ω) :
    indicatorCount (G.erase x) J ω + (J x ω).toNat = indicatorCount G J ω := by
  exact sum_erase_add _ _ hx

omit [Fintype Ω] in
theorem count_erase_eq_sub {G : Finset ι} {x : ι} (hx : x ∈ G)
    (J : ι → Ω → Bool) (ω : Ω) :
    indicatorCount (G.erase x) J ω = indicatorCount G J ω - (J x ω).toNat := by
  have h := count_erase_add hx J ω
  omega

omit [Fintype Ω] in
theorem atom_count_deletion {G : Finset ι} {x : ι} (hx : x ∈ G)
    (J : ι → Ω → Bool) (ω : Ω) :
    (atom (indicatorCount G J ω) : SignedLaw ℝ) = atom (indicatorCount (G.erase x) J ω) +
      scalar (indicatorValue (J x ω)) * forwardDifference * atom (indicatorCount (G.erase x) J ω) := by
  have hc := count_erase_add hx J ω
  cases hJ : J x ω with
  | false =>
    simp only [hJ, Bool.toNat_false, add_zero] at hc
    simp only [← hc, indicatorValue, Bool.false_eq_true, ↓reduceIte, map_zero,
      zero_mul, add_zero]
  | true =>
    simp only [hJ, Bool.toNat_true] at hc
    rw [← hc]
    simp only [indicatorValue, ↓reduceIte, map_one, one_mul, forwardDifference,
      sub_mul, atom_zero]
    have hatom : (atom (indicatorCount (G.erase x) J ω + 1) : SignedLaw ℝ) =
        atom 1 * atom (indicatorCount (G.erase x) J ω) := by
      simp only [atom, AddMonoidAlgebra.single_mul_single, one_mul, Nat.add_comm]
    rw [hatom]
    ring

theorem countLaw_deletion {G : Finset ι} {x : ι} (hx : x ∈ G)
    (w : Ω → ℝ) (J : ι → Ω → Bool) :
    countLaw G w J = countLaw (G.erase x) w J + forwardDifference * activeLaw G w J x := by
  unfold activeLaw countLaw
  rw [mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro ω _
  rw [atom_count_deletion hx J ω, mul_add, map_mul]
  ring

omit [DecidableEq ι] in
theorem sizeWeightedLaw_coeff (G : Finset ι) (w : Ω → ℝ) (J : ι → Ω → Bool) (k : ℕ) :
    (sizeWeightedLaw G w J).coeff k = (k : ℝ) * (countLaw G w J).coeff k := by
  classical
  simp only [sizeWeightedLaw, scalar_mul_atom, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply, countLaw_coeff, mul_sum]
  apply sum_congr rfl
  intro ω _
  by_cases hk : indicatorCount G J ω = k <;> simp [hk, mul_comm]

theorem sizeWeightedLaw_eq_shift_active (G : Finset ι) (w : Ω → ℝ)
    (J : ι → Ω → Bool) :
    sizeWeightedLaw G w J = atom 1 * ∑ x ∈ G, activeLaw G w J x := by
  classical
  have hind (b : Bool) : (b.toNat : ℝ) = indicatorValue b := by cases b <;> simp [indicatorValue]
  unfold sizeWeightedLaw activeLaw countLaw
  simp_rw [indicatorCount, Nat.cast_sum, hind, mul_sum, map_sum, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro x hx
  apply sum_congr rfl
  intro ω _
  have hc := count_erase_add hx J ω
  cases hJ : J x ω with
  | false => simp only [indicatorValue, Bool.false_eq_true, ↓reduceIte, mul_zero,
      map_zero, zero_mul, mul_zero]
  | true =>
    simp only [hJ, Bool.toNat_true] at hc
    change scalar (w ω * indicatorValue true) * atom (indicatorCount G J ω) =
      atom 1 * (scalar (w ω * indicatorValue true) * atom (indicatorCount (G.erase x) J ω))
    rw [← hc]
    rw [scalar_mul_atom, scalar_mul_atom]
    simp only [atom, AddMonoidAlgebra.single_mul_single, one_mul, Nat.add_comm]

theorem deleted_law_sum_identity (G : Finset ι) (w : Ω → ℝ) (J : ι → Ω → Bool) :
    (∑ x ∈ G, countLaw (G.erase x) w J) +
      forwardDifference * (∑ x ∈ G, activeLaw G w J x) =
        scalar (G.card : ℝ) * countLaw G w J := by
  rw [mul_sum, ← sum_add_distrib]
  have h : (∑ x ∈ G, (countLaw (G.erase x) w J + forwardDifference * activeLaw G w J x)) =
      ∑ _x ∈ G, countLaw G w J :=
    sum_congr rfl fun x hx ↦ (countLaw_deletion hx w J).symm
  rw [h]
  simp only [sum_const, nsmul_eq_mul, map_natCast]

end PaperP1.IndicatorDeletion
