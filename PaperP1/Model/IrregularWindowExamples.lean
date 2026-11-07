module

public import PaperP1.Model.ExactRankPrimeCylinderExample
public import PaperP1.Model.NominalRunReplicaFormula
public import PaperP1.Model.HomogeneousRunMass

/-! # Concrete irregular windows separate nominal, effective and homogeneous mass

The start at 18 with length 10 has rank nine and probability 2^-9.
Its one-window effective relative nullity is zero, so substituting that
nullity into a formula with the nominal factor 2^-10 gives a false value.
The start at 3 with length seven is impossible, while its homogeneous
event has positive probability. These finite examples explain two
notation distinctions without changing any numbered manuscript result.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace PaperP1.IrregularWindowExamples

open Finset PaperP1.Model PaperP1.Arithmetic PaperP1.Affine
  PaperP1.ExactRankPrimeCylinderExample PaperP1.Model.InfiniteStarts

local instance primeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

local notation "p2" => (⟨⟨2, by decide⟩, by decide⟩ : PrimeUpTo 28)
local notation "p3" => (⟨⟨3, by decide⟩, by decide⟩ : PrimeUpTo 28)
local notation "p5" => (⟨⟨5, by decide⟩, by decide⟩ : PrimeUpTo 28)
local notation "p7" => (⟨⟨7, by decide⟩, by decide⟩ : PrimeUpTo 28)
local notation "p11" => (⟨⟨11, by decide⟩, by decide⟩ : PrimeUpTo 28)
local notation "p13" => (⟨⟨13, by decide⟩, by decide⟩ : PrimeUpTo 28)
local notation "p17" => (⟨⟨17, by decide⟩, by decide⟩ : PrimeUpTo 28)
local notation "p19" => (⟨⟨19, by decide⟩, by decide⟩ : PrimeUpTo 28)
local notation "p23" => (⟨⟨23, by decide⟩, by decide⟩ : PrimeUpTo 28)

theorem kernel_eq_bot : LinearMap.ker (startSystem 28 18 10) = ⊥ := by
  apply LinearMap.ker_eq_bot'.mpr
  intro σ hσ
  have row (j : ℕ) (hj : j < 10) (hj0 : j ≠ 0) :
      valueBit σ 18 + valueBit σ (18+j) = 0 := by
    have h := congrFun hσ (⟨j,hj⟩ : Fin 10)
    simpa only [startSystem_apply, hj0, ite_false, Pi.zero_apply] using h
  have h18 : valueBit σ 18 = 0 := by
    have h := row 7 (by decide) (by decide)
    rw [show (18+7 : ℕ) = 5^2 by decide, square_value, add_zero] at h
    exact h
  have word (j : ℕ) (hj : j < 10) (hj0 : j ≠ 0) :
      valueBit σ (18+j) = 0 := by
    have h := row j hj hj0
    simpa only [h18, zero_add] using h
  have h2 : σ p2 = 0 := by
    have h := h18
    rw [show (18 : ℕ) = 3^2*2 by decide,
      valueBit_mul σ (by decide) (by decide), square_value, zero_add, prime_value σ p2] at h
    exact h
  have h3 : σ p3 = 0 := by
    have h := word 9 (by decide) (by decide)
    rw [show (18+9 : ℕ) = 3^2*3 by decide,
      valueBit_mul σ (by decide) (by decide), square_value, zero_add, prime_value σ p3] at h
    exact h
  have h5 : σ p5 = 0 := by
    have h := word 2 (by decide) (by decide)
    rw [show (18+2 : ℕ) = 2^2*5 by decide,
      valueBit_mul σ (by decide) (by decide), square_value, zero_add, prime_value σ p5] at h
    exact h
  have h7 : σ p7 = 0 := by
    have h := word 3 (by decide) (by decide)
    rw [show (18+3 : ℕ) = 3*7 by decide,
      valueBit_mul σ (by decide) (by decide), prime_value σ p3, prime_value σ p7, h3, zero_add] at h
    exact h
  have h11 : σ p11 = 0 := by
    have h := word 4 (by decide) (by decide)
    rw [show (18+4 : ℕ) = 2*11 by decide,
      valueBit_mul σ (by decide) (by decide), prime_value σ p2, prime_value σ p11, h2, zero_add] at h
    exact h
  have h13 : σ p13 = 0 := by
    have h := word 8 (by decide) (by decide)
    rw [show (18+8 : ℕ) = 2*13 by decide,
      valueBit_mul σ (by decide) (by decide), prime_value σ p2, prime_value σ p13, h2, zero_add] at h
    exact h
  have h17 : σ p17 = 0 := by
    have h := congrFun hσ (⟨0,by decide⟩ : Fin 10)
    simpa only [startSystem_apply, ite_true, Pi.zero_apply, h18, add_zero,
      show (18-1 : ℕ) = (p17).val.val by rfl, prime_value σ p17] using h
  have h19 : σ p19 = 0 := by
    have h := word 1 (by decide) (by decide)
    rw [show (18+1 : ℕ) = (p19).val.val by rfl, prime_value σ p19] at h
    exact h
  have h23 : σ p23 = 0 := by
    have h := word 5 (by decide) (by decide)
    rw [show (18+5 : ℕ) = (p23).val.val by rfl, prime_value σ p23] at h
    exact h
  have hprimes : ∀ p : PrimeUpTo 28,
      p.val.val ∈ ({2,3,5,7,11,13,17,19,23} : Finset ℕ) := by decide +kernel
  funext p
  have hp := hprimes p
  simp only [mem_insert, mem_singleton] at hp
  have transport (q : PrimeUpTo 28) (hv : p.val.val = q.val.val)
      (hz : σ q = 0) : σ p = 0 := (congrArg σ (Subtype.ext (Fin.ext hv))).trans hz
  rcases hp with hp|hp|hp|hp|hp|hp|hp|hp|hp
  all_goals first
    | exact transport p2 hp h2
    | exact transport p3 hp h3
    | exact transport p5 hp h5
    | exact transport p7 hp h7
    | exact transport p11 hp h11
    | exact transport p13 hp h13
    | exact transport p17 hp h17
    | exact transport p19 hp h19
    | exact transport p23 hp h23

theorem exact_rank : startRank 28 18 10 = 9 := by
  have h := (startSystem 28 18 10).finrank_range_add_finrank_ker
  rw [kernel_eq_bot, finrank_bot, add_zero, Module.finrank_fintype_fun_eq_card] at h
  have hc : Fintype.card (PrimeUpTo 28) = 9 := by decide +kernel
  simpa only [startRank, hc] using h

theorem compatible : Compatible (startSystem 28 18 10) (startRhs 10) := by
  have h := (OneNegativePrime.positive_exact_run p17 1 (by decide) (by decide)).1
  change StartEvent (valueBit (OneNegativePrime.sample p17)) 18 16 at h
  apply LinearMap.mem_range.mpr
  refine ⟨OneNegativePrime.sample p17, (startSystem_eq_startRhs_iff _ (by decide)).mpr ?_⟩
  exact ⟨h.1, fun j hj ↦ h.2 j (by omega)⟩

theorem exact_marginal : infiniteMarginal 18 10 = (512 : ℝ)⁻¹ := by
  rw [infiniteMarginal_eq_finite (M := 28) (by decide),
    exactMarginal_start_of_compatible 28 18 10 (by decide) compatible, exact_rank]
  norm_num

theorem raw_relation_dimension :
    Module.finrank F₂ (LinearMap.ker (relationMap (startSystem 28 18 10))) = 1 := by
  have h := NominalAffineMass.compatible (startSystem 28 18 10) (startRhs 10) compatible
  have hm : uniformSolutionMass (startSystem 28 18 10) (startRhs 10) = (512 : ℝ)⁻¹ := by
    rw [uniformSolutionMass_of_compatible _ _ compatible]
    change (2^startRank 28 18 10 : ℝ)⁻¹ = _
    rw [exact_rank]
    norm_num
  rw [hm, Fintype.card_fin] at h
  norm_num at h
  apply Nat.pow_right_injective (by decide : 2 ≤ 2)
  have hp : (2 : ℝ)^Module.finrank F₂
      (LinearMap.ker (relationMap (startSystem 28 18 10))) = (2 : ℝ)^1 := by
    norm_num
    linarith
  exact_mod_cast hp

theorem effective_kernel_nominal_fails :
    infiniteMarginal 18 10 ≠
      (2^10 : ℝ)⁻¹ * (2^runRelativeNullity 10 {18} : ℝ) := by
  rw [exact_marginal]
  simp only [runRelativeNullity, RetainedNullity.nullity_singleton, pow_zero, mul_one]
  norm_num

theorem short_window_impossible {M : ℕ} (σ : SampleSpace M) :
    ¬StartEvent (valueBit σ) 3 7 := by
  intro h
  have h3 : valueBit σ 3 = 0 := by
    have h4 := h.2 1 (by decide)
    rw [show (3+1 : ℕ) = 2^2 by decide, square_value] at h4
    exact h4.symm
  have h2 : valueBit σ 2 = 0 := by
    have h6 := h.2 3 (by decide)
    rw [show (3+3 : ℕ) = 2*3 by decide,
      valueBit_mul σ (by decide) (by decide), h3, add_zero] at h6
    exact h6
  have hboundary := h.1
  norm_num [h2,h3] at hboundary

theorem zero_marginal : infiniteMarginal 3 7 = 0 := by
  rw [infiniteMarginal_eq_finite (M := 10) (by decide)]
  apply exactMarginal_start_of_not_compatible 10 3 7 (by decide)
  intro hc
  obtain ⟨σ,hσ⟩ := LinearMap.mem_range.mp hc
  exact short_window_impossible σ ((startSystem_eq_startRhs_iff σ (by decide)).mp hσ)

theorem homogeneous_positive_original_zero :
    0 < HomogeneousRunMass.probability 7 {3} ∧ infiniteMarginal 3 7 = 0 :=
  ⟨HomogeneousRunMass.probability_pos 7 {3}, zero_marginal⟩

end PaperP1.IrregularWindowExamples
