module

public import PaperP1.Affine.BinaryMassLattice
public import PaperP1.Probability.SubsetFactorials
public import PaperP1.Model.FactorialCountMoments
public import PaperP1.Model.RunSeparation

/-! # Companion T19.1: exact support and factorial lattice

Each actual joint event has a binary system with at most |I|L equations.
Its mass is an integer multiple of p^|I|, including the incompatible case.
The unordered-subset factorial identity supplies the additional factor j!.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RunCountLattice

open PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
open PaperP1.Model.InfiniteRademacher PaperP1.Probability PaperP1.Algebra
open CountObservables FactorialCountMoments RunSeparation Finset

local instance runCountLatticePrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

theorem joint_moment_nominal_lattice (L : ℕ) (hL : 0 < L) (I : Finset ℕ) :
    ∃ m : ℕ, infiniteJointMoment L I = (m : ℝ) * ((2 ^ L : ℝ)⁻¹) ^ I.card := by
  classical
  let M := I.sup (fun x ↦ x + L)
  have hcut : ∀ x ∈ I, x + L ≤ M := fun x hx ↦ le_sup (f := fun x ↦ x + L) hx
  let A := familyStartSystem M L (fun x : I ↦ x.val)
  have hdim : Module.finrank F₂ (I × Fin L → F₂) = I.card * L := by
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_prod,
      Fintype.card_coe, Fintype.card_fin]
  have hrank : Module.finrank F₂ (LinearMap.range A) ≤ I.card * L :=
    (Submodule.finrank_le _).trans_eq hdim
  obtain ⟨m, hm⟩ := uniformSolutionMass_integer_multiple A (familyStartRhs L) (I.card * L) hrank
  have hnom : ((2 ^ L : ℝ)⁻¹) ^ I.card = (2 ^ (I.card * L) : ℝ)⁻¹ := by
    calc
      _ = (2 ^ (L * I.card) : ℝ)⁻¹ := by rw [pow_mul, inv_pow]
      _ = _ := congrArg (fun n : ℕ ↦ (2 ^ n : ℝ)⁻¹) (Nat.mul_comm L I.card)
  refine ⟨m, ?_⟩
  rw [infiniteJointMoment_eq_startFamily M L I hcut,
    startFamilyJointMoment_eq_affineMass M L _ hL, hnom]
  exact hm

theorem factorialCountMoment_eq_subset_sum {N L : ℕ} {G : Finset ℕ}
    (hG : G ⊆ dyadicBlock N) (j : ℕ) :
    factorialCountMoment G L j = (j.factorial : ℝ) *
      ∑ I ∈ G.powersetCard j, infiniteJointMoment L I := by
  rw [factorialCountMoment_eq_finite hG]
  calc
    _ = finiteExpectation (cylinderProbability (dyadicCutoff N L)).weight
        (fun σ ↦ (j.factorial : ℝ) * ∑ I ∈ G.powersetCard j,
          ∏ x ∈ I, (indicatorValue (startIndicator x L σ) : ℝ)) := by
      congr 1
      funext σ
      exact factorial_subset_expansion G (fun x ↦ startIndicator x L) σ j
    _ = (j.factorial : ℝ) * ∑ I ∈ G.powersetCard j,
        finiteExpectation (cylinderProbability (dyadicCutoff N L)).weight
          (fun σ ↦ ∏ x ∈ I, (indicatorValue (startIndicator x L σ) : ℝ)) := by
      rw [finiteExpectation_const_mul, finiteExpectation_sum]
    _ = _ := by
      congr 1
      apply sum_congr rfl
      intro I hI
      exact (infiniteJointMoment_eq_finite (dyadicCutoff N L) L I
        (dyadic_subset_cutoff ((mem_powersetCard.mp hI).1.trans hG))).symm

theorem factorial_count_lattice {N L : ℕ} {G : Finset ℕ}
    (hG : G ⊆ dyadicBlock N) (hL : 0 < L) (j : ℕ) :
    ∃ m : ℕ, factorialCountMoment G L j =
      (j.factorial : ℝ) * ((2 ^ L : ℝ)⁻¹) ^ j * (m : ℝ) := by
  classical
  let m : Finset ℕ → ℕ := fun I ↦ Classical.choose (joint_moment_nominal_lattice L hL I)
  have hm (I : Finset ℕ) : infiniteJointMoment L I =
      (m I : ℝ) * ((2 ^ L : ℝ)⁻¹) ^ I.card :=
    Classical.choose_spec (joint_moment_nominal_lattice L hL I)
  refine ⟨∑ I ∈ G.powersetCard j, m I, ?_⟩
  rw [factorialCountMoment_eq_subset_sum hG]
  have hsum : (∑ I ∈ G.powersetCard j, infiniteJointMoment L I) =
      ((∑ I ∈ G.powersetCard j, m I : ℕ) : ℝ) * ((2 ^ L : ℝ)⁻¹) ^ j := by
    calc
      _ = ∑ I ∈ G.powersetCard j, (m I : ℝ) * ((2 ^ L : ℝ)⁻¹) ^ j := by
        apply sum_congr rfl
        intro I hI
        rw [hm I, (mem_powersetCard.mp hI).2]
      _ = _ := by rw [← sum_mul, Nat.cast_sum]
  rw [hsum]
  ring

/-- Full manuscript proposition, with the nonnegative lattice coefficient
represented by an actual natural number. -/
theorem companion_T19_1 {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) :
    (∀ ω : InfiniteSample, 0 ≤ infiniteStartCount (dyadicBlock N) L ω ∧
      infiniteStartCount (dyadicBlock N) L ω ≤ ⌈(N : ℝ) / L⌉₊) ∧
    ∀ j : ℕ, 1 ≤ j → ∃ m : ℕ, factorialCountMoment (dyadicBlock N) L j =
      (j.factorial : ℝ) * ((2 ^ L : ℝ)⁻¹) ^ j * (m : ℝ) := by
  refine ⟨dyadic_count_support hN hL, fun j _hj ↦ ?_⟩
  exact factorial_count_lattice (subset_refl _) hL j

theorem dyadicCountLaw_coeff_eq_zero_above_support {N L k : ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (hk : ⌈(N : ℝ) / L⌉₊ < k) :
    (dyadicCountLaw N L).coeff k = 0 := by
  rw [dyadicCountLaw_coeff_eq_infinite_probability]
  have hempty : {ω : InfiniteSample | infiniteStartCount (dyadicBlock N) L ω = k} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ω hω
    have hcount := (dyadic_count_support hN hL ω).2
    change infiniteStartCount (dyadicBlock N) L ω = k at hω
    omega
  rw [hempty]
  simp

theorem dyadicCountLaw_support_subset {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) :
    (dyadicCountLaw N L).coeff.support ⊆ range (⌈(N : ℝ) / L⌉₊ + 1) := by
  intro k hk
  apply mem_range.mpr
  by_contra hnot
  have hlarge : ⌈(N : ℝ) / L⌉₊ < k := by omega
  exact (Finsupp.mem_support_iff.mp hk) (dyadicCountLaw_coeff_eq_zero_above_support hN hL hlarge)

end PaperP1.RunCountLattice
