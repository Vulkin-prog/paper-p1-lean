module

public import PaperP1.Affine.Subfamilies
public import PaperP1.Algebra.Centering
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The compatible-nullity maximum and its algebraic majorant

The maximum is taken only over positive actual joint masses. The algebraic
bound below has an explicit exact-joint-mass premise; later model theorems
must prove that premise from their affine events, rather than assuming the
desired centered bound.
-/

@[expose] public noncomputable section

open scoped BigOperators
open PaperP1.Algebra

namespace PaperP1.Affine

local instance compatibleNullityDecidable (P : Prop) : Decidable P := Classical.propDecidable P
local instance compatibleNullityPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

variable {U κ : Type*} [AddCommGroup U] [Module 𝔽₂ U] [DecidableEq κ]
variable (S : κ → Submodule 𝔽₂ U) [∀ i, Fintype (S i)]

def compatibleNullityOn (q : Finset κ → ℝ) (I : Finset κ) : ℕ :=
  I.powerset.sup fun A => if 0 < q A then relativeNullityOn S A else 0

omit [DecidableEq κ] in
theorem relativeNullityOn_empty : relativeNullityOn S ∅ = 0 := by
  rw [relativeNullityOn, relativeNullity_eq_dimension_deficit]
  simp

omit [DecidableEq κ] [∀ i, Fintype (S i)] in
theorem relativeNullityOn_le_compatibleNullityOn (q : Finset κ → ℝ)
    {A I : Finset κ} (hsub : A ⊆ I) (hq : 0 < q A) :
    relativeNullityOn S A ≤ compatibleNullityOn S q I := by
  have h := Finset.le_sup (f := fun B => if 0 < q B then relativeNullityOn S B else 0)
    (Finset.mem_powerset.mpr hsub)
  rwa [ite_eq_left hq] at h

theorem compatibleNullityOn_le (q : Finset κ → ℝ) (I : Finset κ) :
    compatibleNullityOn S q I ≤ relativeNullityOn S I := by
  apply Finset.sup_le
  intro A hA
  split_ifs
  · exact relativeNullityOn_mono S (Finset.mem_powerset.mp hA)
  · exact Nat.zero_le _

theorem compatibleNullityOn_eq_of_pos (q : Finset κ → ℝ) (I : Finset κ) (hq : 0 < q I) :
    compatibleNullityOn S q I = relativeNullityOn S I := by
  exact le_antisymm (compatibleNullityOn_le S q I)
    (relativeNullityOn_le_compatibleNullityOn S q Finset.Subset.rfl hq)

omit [DecidableEq κ] in
theorem compatibleNullityOn_empty (q : Finset κ → ℝ) : compatibleNullityOn S q ∅ = 0 := by
  simp [compatibleNullityOn, relativeNullityOn_empty]

omit [∀ i, Fintype (S i)] [DecidableEq κ] in
theorem compatibleNullityOn_eq_filtered_sup (q : Finset κ → ℝ) (I : Finset κ) :
    compatibleNullityOn S q I =
      (I.powerset.filter fun A => 0 < q A).sup (relativeNullityOn S) := by
  apply le_antisymm
  · apply Finset.sup_le
    intro A hA
    split_ifs with hq
    · exact Finset.le_sup (f := relativeNullityOn S) (Finset.mem_filter.mpr ⟨hA, hq⟩)
    · exact Nat.zero_le _
  · apply Finset.sup_le
    intro A hA
    obtain ⟨hsub, hq⟩ := Finset.mem_filter.mp hA
    exact relativeNullityOn_le_compatibleNullityOn S q (Finset.mem_powerset.mp hsub) hq

omit [∀ i, Fintype (S i)] in
theorem centeredCoefficient_compatibleNullity_bound
    (p : κ → ℝ) (q : Finset κ → ℝ) (I : Finset κ)
    (hp : ∀ x ∈ I, 0 < p x)
    (hq_nonneg : ∀ A ⊆ I, 0 ≤ q A)
    (hq_exact : ∀ A ⊆ I, 0 < q A →
      q A = (∏ x ∈ A, p x) * (2 ^ relativeNullityOn S A : ℝ)) :
    |centeredCoefficient p q I| ≤
      (2 ^ I.card : ℝ) * (∏ x ∈ I, p x) * (2 ^ compatibleNullityOn S q I : ℝ) := by
  classical
  have hprod : 0 ≤ ∏ x ∈ I, p x := le_of_lt (Finset.prod_pos hp)
  have hterm (A : Finset κ) (hA : A ∈ I.powerset) :
      |(-1 : ℝ) ^ (I.card - A.card) * q A * ∏ x ∈ I \ A, p x| ≤
        (∏ x ∈ I, p x) * (2 ^ compatibleNullityOn S q I : ℝ) := by
    have hsub : A ⊆ I := Finset.mem_powerset.mp hA
    have hqc : 0 ≤ q A := hq_nonneg A hsub
    have hcomp : 0 ≤ ∏ x ∈ I \ A, p x :=
      Finset.prod_nonneg fun x hx => le_of_lt (hp x (Finset.mem_sdiff.mp hx).1)
    by_cases hpos : 0 < q A
    · have hsplit : (∏ x ∈ A, p x) * (∏ x ∈ I \ A, p x) = ∏ x ∈ I, p x := by
        rw [mul_comm, Finset.prod_sdiff hsub]
      calc
        _ = q A * ∏ x ∈ I \ A, p x := by
          simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
            abs_of_nonneg hqc, abs_of_nonneg hcomp]
        _ = (∏ x ∈ I, p x) * (2 ^ relativeNullityOn S A : ℝ) := by
          rw [hq_exact A hsub hpos]
          calc
            _ = ((∏ x ∈ A, p x) * (∏ x ∈ I \ A, p x)) *
                (2 ^ relativeNullityOn S A : ℝ) := by ring1
            _ = _ := by rw [hsplit]
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
            (relativeNullityOn_le_compatibleNullityOn S q hsub hpos)) hprod
    · have hz : q A = 0 := le_antisymm (le_of_not_gt hpos) hqc
      simp only [hz, mul_zero, zero_mul, abs_zero]
      exact mul_nonneg hprod (by positivity)
  unfold centeredCoefficient
  calc
    _ ≤ ∑ A ∈ I.powerset,
        |(-1 : ℝ) ^ (I.card - A.card) * q A * ∏ x ∈ I \ A, p x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _A ∈ I.powerset,
        (∏ x ∈ I, p x) * (2 ^ compatibleNullityOn S q I : ℝ) :=
      Finset.sum_le_sum hterm
    _ = _ := by
      simp [Finset.card_powerset, nsmul_eq_mul, mul_assoc]

end PaperP1.Affine
