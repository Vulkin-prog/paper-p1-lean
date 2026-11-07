module

public import PaperP1.Model.ValuationDensityBounds
public import PaperP1.Affine.RealProbability

/-! # Charge the effective rank of the actual forcing equations
Negative predecessors and positive words form one compatible affine
system on the actual finite prime-sign space. Its exact mass is 2^-r,
where r is its effective rank, at most the number of prime coordinates.
Both full moments inherit this rank charge and all previous count
budgets. At N=18,q=3 there are five retained starts and eleven prime
coordinates. The unused prime 19 proves r<=10 and hence the lower bound
exp(5*t-10*log 2), a factor-two gain over the same-count atom bound.
No improved asymptotic threshold is asserted.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace PaperP1.RankChargedPrimeCylinder

open Finset PaperP1.Model PaperP1.Arithmetic PaperP1.Affine
  PaperP1.Algebra PaperP1.Probability PaperP1.LocalDefectBound

local instance rankCylinderPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

def row (M x L : ℕ) (i : Option (Fin L)) : SampleSpace M →ₗ[F₂] F₂ :=
  match i with
  | none => valueLinear M (x-1)
  | some j => valueLinear M (x+j.val)

def system (M : ℕ) (G : Finset ℕ) (L : ℕ) :
    SampleSpace M →ₗ[F₂] (↥G × Option (Fin L) → F₂) :=
  LinearMap.pi fun i ↦ row M i.1.val L i.2

def rhs (G : Finset ℕ) (L : ℕ) : ↥G × Option (Fin L) → F₂ :=
  fun i ↦ match i.2 with | none => 1 | some _ => 0

def rank (M : ℕ) (G : Finset ℕ) (L : ℕ) : ℕ :=
  Module.finrank F₂ (LinearMap.range (system M G L))

def retainedRank (N q : ℕ) : ℕ :=
  rank (SupportedPrimeCylinder.cutoff N q) (ValuationPrimeCylinder.starts N q) (q-1)

theorem system_apply_none {M L : ℕ} {G : Finset ℕ} (σ : SampleSpace M) (x : G) :
    system M G L σ (x,none)=valueBit σ (x.val-1) := rfl

theorem system_apply_some {M L : ℕ} {G : Finset ℕ} (σ : SampleSpace M) (x : G) (j : Fin L) :
    system M G L σ (x,some j)=valueBit σ (x.val+j.val) := rfl

theorem system_eq_rhs_iff {M L : ℕ} {G : Finset ℕ} (hL : 0<L) (σ : SampleSpace M) :
    system M G L σ=rhs G L ↔
      ∀ x∈G, StartEvent (valueBit σ) x L ∧ valueBit σ x=0 := by
  constructor
  · intro h x hx
    have hprev := congrFun h (⟨x,hx⟩,none)
    have hfirst := congrFun h (⟨x,hx⟩,some ⟨0,hL⟩)
    change valueBit σ (x-1)=1 at hprev
    change valueBit σ (x+0)=0 at hfirst
    rw [Nat.add_zero] at hfirst
    refine ⟨⟨?_,?_⟩,hfirst⟩
    · rw [hprev,hfirst,add_zero]
    · intro j hj
      have hrow := congrFun h (⟨x,hx⟩,some ⟨j,hj⟩)
      change valueBit σ (x+j)=0 at hrow
      rw [hrow,hfirst]
  · intro h
    funext i
    obtain ⟨x,i⟩ := i
    obtain ⟨hstart,hfirst⟩ := h x.val x.property
    cases i with
    | none =>
      change valueBit σ (x.val-1)=1
      simpa only [hfirst,add_zero] using hstart.1
    | some j =>
      change valueBit σ (x.val+j.val)=0
      rw [hstart.2 j.val j.isLt,hfirst]

theorem count_eq_card_of_solution {M L : ℕ} {G : Finset ℕ} (hL : 0<L) (σ : SampleSpace M)
    (h : system M G L σ=rhs G L) :
    indicatorCount G (fun x ↦ PositiveStarts.indicator x L) σ=G.card := by
  have hstarts := (system_eq_rhs_iff hL σ).mp h
  unfold indicatorCount
  calc
    _ = ∑ _x ∈ G,1 := by
      apply sum_congr rfl
      intro x hx
      have hI : PositiveStarts.indicator x L σ=true := by
        simp only [PositiveStarts.indicator,Bool.and_eq_true,decide_eq_true_eq,startIndicator_eq_true_iff]
        exact hstarts x hx
      change (PositiveStarts.indicator x L σ).toNat=1
      rw [hI]
      rfl
    _ = G.card := by simp

theorem rank_le_primeCount (M : ℕ) (G : Finset ℕ) (L : ℕ) : rank M G L≤primeCount M := by
  have hdim := (system M G L).finrank_range_add_finrank_ker
  rw [Module.finrank_fintype_fun_eq_card,PrimeCylinderSize.prime_card] at hdim
  unfold rank
  omega

theorem exact_forcing_mass {M L : ℕ} {G : Finset ℕ}
    (h : Compatible (system M G L) (rhs G L)) :
    uniformSolutionMass (system M G L) (rhs G L)=(2^(rank M G L) : ℝ)⁻¹ :=
  uniformSolutionMass_of_compatible _ _ h

theorem finite_exponential_mass_lower {M L : ℕ} {G : Finset ℕ} (hL : 0<L) (t : ℝ) :
    uniformSolutionMass (system M G L) (rhs G L)*Real.exp (t*(G.card : ℝ))≤
      finiteExpectation (cylinderProbability M).weight
        (fun σ ↦ Real.exp (t*(indicatorCount G (fun x ↦ PositiveStarts.indicator x L) σ : ℝ))) := by
  classical
  rw [uniformSolutionMass]
  rw [← finiteExpectation_mul_const]
  unfold finiteExpectation
  apply sum_le_sum
  intro σ _
  apply mul_le_mul_of_nonneg_left _ ((cylinderProbability M).weight_nonneg σ)
  by_cases h : system M G L σ=rhs G L
  · simp only [ite_eq_left h,one_mul,count_eq_card_of_solution hL σ h]
    exact le_rfl
  · simp only [ite_eq_right h,zero_mul]
    exact (Real.exp_pos _).le

theorem retained_compatible {N q : ℕ} (hq : Nat.Prime q) (hqN : q≤N) :
    Compatible (system (SupportedPrimeCylinder.cutoff N q) (ValuationPrimeCylinder.starts N q) (q-1))
      (rhs (ValuationPrimeCylinder.starts N q) (q-1)) := by
  let M := SupportedPrimeCylinder.cutoff N q
  let p : PrimeUpTo M := ⟨⟨q,by
    have hdiv : 1≤N/q := (Nat.le_div_iff_mul_le hq.pos).mpr (by simpa only [one_mul] using hqN)
    have hmul := Nat.mul_le_mul_left (2*q) hdiv
    dsimp [M,SupportedPrimeCylinder.cutoff]
    nlinarith⟩,hq⟩
  apply LinearMap.mem_range.mpr
  refine ⟨OneNegativePrime.sample p,(system_eq_rhs_iff (by have h := hq.two_le; omega) _).mpr ?_⟩
  intro x hx
  obtain ⟨u,hu,hbit,rfl⟩ := (ValuationPrimeCylinder.mem_starts N q x).mp hx
  have huPos := ValuationDensityBounds.parameters_positive hu
  exact (ValuationPrimeCylinder.positive_start_iff p u huPos).mpr hbit

theorem retained_rank_le_primeCount (N q : ℕ) :
    retainedRank N q≤primeCount (SupportedPrimeCylinder.cutoff N q) :=
  rank_le_primeCount _ _ _

theorem retained_forcing_mass {N q : ℕ} (hq : Nat.Prime q) (hqN : q≤N) :
    uniformSolutionMass
      (system (SupportedPrimeCylinder.cutoff N q) (ValuationPrimeCylinder.starts N q) (q-1))
      (rhs (ValuationPrimeCylinder.starts N q) (q-1))=(2^retainedRank N q : ℝ)⁻¹ :=
  exact_forcing_mass (retained_compatible hq hqN)

theorem positive_exponential_card_lower {N q : ℕ} (hq : Nat.Prime q) (hqN : q≤N)
    (t : ℝ) (ht : 0≤t) :
    Real.exp (t*((ValuationPrimeCylinder.starts N q).card : ℝ)-
      (retainedRank N q : ℝ)*Real.log 2)≤
        PositiveStarts.exponentialMoment (dyadicBlock N) (q-1) t := by
  let M := SupportedPrimeCylinder.cutoff N q
  let G := ValuationPrimeCylinder.starts N q
  have hfinite := finite_exponential_mass_lower (M:=M) (G:=G)
    (by have h := hq.two_le; omega : 0<q-1) t
  rw [retained_forcing_mass hq hqN] at hfinite
  have heq : Real.exp (t*(G.card : ℝ)-(retainedRank N q : ℝ)*Real.log 2)=
      (2^retainedRank N q : ℝ)⁻¹*Real.exp (t*(G.card : ℝ)) := by
    rw [Real.exp_sub,Real.exp_nat_mul,Real.exp_log (by norm_num : (0 : ℝ)<2)]
    ring
  have hsmall : Real.exp (t*(G.card : ℝ)-(retainedRank N q : ℝ)*Real.log 2)≤
      PositiveStarts.exponentialMoment G (q-1) t := by
    rw [SupportedPrimeCylinder.positive_moment_eq_finite
      (ValuationPrimeCylinder.retained_starts_cutoff hq.two_le hqN),heq]
    exact hfinite
  exact hsmall.trans (SupportedPrimeCylinder.positive_moment_mono
    (ValuationPrimeCylinder.starts_subset_interval hq.two_le hqN) (q-1) t ht)

theorem total_exponential_card_lower {N q : ℕ} (hq : Nat.Prime q) (hqN : q≤N)
    (t : ℝ) (ht : 0≤t) :
    Real.exp (t*((ValuationPrimeCylinder.starts N q).card : ℝ)-
      (retainedRank N q : ℝ)*Real.log 2)≤
        PrimeRunCylinder.totalExponentialMoment N (q-1) t :=
  (positive_exponential_card_lower hq hqN t ht).trans (PrimeRunCylinder.positive_le_total N (q-1) t ht)

theorem positive_exponential_layer_lower {N q : ℕ} (hq : Nat.Prime q) (hqN : q≤N)
    (k : ℕ) (t : ℝ) (ht : 0≤t) :
    Real.exp (t*ValuationLayerCounts.budget N q k-(retainedRank N q : ℝ)*Real.log 2)≤
      PositiveStarts.exponentialMoment (dyadicBlock N) (q-1) t :=
  (Real.exp_le_exp.mpr (sub_le_sub_right (mul_le_mul_of_nonneg_left
    (ValuationLayerCounts.finite_geometric_lower hq.two_le hqN k) ht) _)).trans
      (positive_exponential_card_lower hq hqN t ht)

theorem positive_exponential_density_lower {N q : ℕ} (hq : Nat.Prime q) (hqN : q≤N)
    (t : ℝ) (ht : 0≤t) :
    Real.exp (t*ValuationDensityBounds.lowerBudget N q-(retainedRank N q : ℝ)*Real.log 2)≤
      PositiveStarts.exponentialMoment (dyadicBlock N) (q-1) t :=
  (Real.exp_le_exp.mpr (sub_le_sub_right (mul_le_mul_of_nonneg_left
    (ValuationDensityBounds.starts_card_lower hq.two_le hqN) ht) _)).trans
      (positive_exponential_card_lower hq hqN t ht)

theorem total_exponential_layer_lower {N q : ℕ} (hq : Nat.Prime q) (hqN : q≤N)
    (k : ℕ) (t : ℝ) (ht : 0≤t) :
    Real.exp (t*ValuationLayerCounts.budget N q k-(retainedRank N q : ℝ)*Real.log 2)≤
      PrimeRunCylinder.totalExponentialMoment N (q-1) t :=
  (positive_exponential_layer_lower hq hqN k t ht).trans
    (PrimeRunCylinder.positive_le_total N (q-1) t ht)

theorem total_exponential_density_lower {N q : ℕ} (hq : Nat.Prime q) (hqN : q≤N)
    (t : ℝ) (ht : 0≤t) :
    Real.exp (t*ValuationDensityBounds.lowerBudget N q-(retainedRank N q : ℝ)*Real.log 2)≤
      PrimeRunCylinder.totalExponentialMoment N (q-1) t :=
  (positive_exponential_density_lower hq hqN t ht).trans
    (PrimeRunCylinder.positive_le_total N (q-1) t ht)

theorem rank_cost_refines_prime_cost (N q : ℕ) (t : ℝ) :
    Real.exp (t*((ValuationPrimeCylinder.starts N q).card : ℝ)-
      (primeCount (SupportedPrimeCylinder.cutoff N q) : ℝ)*Real.log 2)≤
    Real.exp (t*((ValuationPrimeCylinder.starts N q).card : ℝ)-
      (retainedRank N q : ℝ)*Real.log 2) := by
  have hr : (retainedRank N q : ℝ)≤primeCount (SupportedPrimeCylinder.cutoff N q) := by
    exact_mod_cast retained_rank_le_primeCount N q
  have hlog : (0 : ℝ)≤Real.log 2 := Real.log_nonneg (by norm_num)
  apply Real.exp_le_exp.mpr
  nlinarith

theorem sample_ne_zero {M : ℕ} (p : PrimeUpTo M) : OneNegativePrime.sample p≠0 := by
  intro hzero
  have h := congrFun hzero p
  simp [OneNegativePrime.sample] at h

theorem unused_prime_in_ker {M L : ℕ} {G : Finset ℕ} (p : PrimeUpTo M)
    (h : ∀ x∈G, ¬p.val.val∣x-1 ∧ ∀ j : ℕ, j<L → ¬p.val.val∣x+j) :
    OneNegativePrime.sample p∈LinearMap.ker (system M G L) := by
  apply LinearMap.mem_ker.mpr
  funext i
  obtain ⟨x,i⟩ := i
  cases i with
  | none =>
    change valueBit (OneNegativePrime.sample p) (x.val-1)=0
    rw [OneNegativePrime.valueBit_sample]
    exact OneNegativePrime.parity_zero_of_not_dvd (h x.val x.property).1
  | some j =>
    change valueBit (OneNegativePrime.sample p) (x.val+j.val)=0
    rw [OneNegativePrime.valueBit_sample]
    exact OneNegativePrime.parity_zero_of_not_dvd ((h x.val x.property).2 j.val j.isLt)

theorem rank_lt_primeCount_of_unused {M L : ℕ} {G : Finset ℕ} (p : PrimeUpTo M)
    (h : ∀ x∈G, ¬p.val.val∣x-1 ∧ ∀ j : ℕ, j<L → ¬p.val.val∣x+j) :
    rank M G L<primeCount M := by
  let z : LinearMap.ker (system M G L) := ⟨OneNegativePrime.sample p,unused_prime_in_ker p h⟩
  have hz : z≠0 := by
    intro heq
    exact sample_ne_zero p (congrArg Subtype.val heq)
  have hpos : 0<Module.finrank F₂ (LinearMap.ker (system M G L)) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨z,hz⟩
  have hdim := (system M G L).finrank_range_add_finrank_ker
  rw [Module.finrank_fintype_fun_eq_card,PrimeCylinderSize.prime_card] at hdim
  unfold rank
  omega

def unusedPrimeExample : PrimeUpTo (SupportedPrimeCylinder.cutoff 18 3) :=
  ⟨⟨19,by norm_num [SupportedPrimeCylinder.cutoff]⟩,by decide⟩

theorem unused_prime_example :
    ∀ x∈ValuationPrimeCylinder.starts 18 3,
      ¬19∣x-1 ∧ ∀ j : ℕ, j<2 → ¬19∣x+j := by
  intro x hx
  obtain ⟨u,hu,_hbit,rfl⟩ := (ValuationPrimeCylinder.mem_starts 18 3 x).mp hx
  have hu' : 7≤u ∧ u<12 := by simpa [PrimeRunStarts.parameters] using hu
  constructor
  · rintro ⟨a,ha⟩
    omega
  · intro j hj
    have hval : 21≤3*u+1+j ∧ 3*u+1+j<38 := by omega
    rintro ⟨a,ha⟩
    omega

theorem strict_rank_gain_example :
    retainedRank 18 3<primeCount (SupportedPrimeCylinder.cutoff 18 3) :=
  rank_lt_primeCount_of_unused unusedPrimeExample unused_prime_example

theorem factor_two_gain_of_rank_drop (N q : ℕ)
    (h : retainedRank N q<primeCount (SupportedPrimeCylinder.cutoff N q)) (t : ℝ) :
    2*Real.exp (t*((ValuationPrimeCylinder.starts N q).card : ℝ)-
      (primeCount (SupportedPrimeCylinder.cutoff N q) : ℝ)*Real.log 2)≤
    Real.exp (t*((ValuationPrimeCylinder.starts N q).card : ℝ)-
      (retainedRank N q : ℝ)*Real.log 2) := by
  have hstep : (retainedRank N q : ℝ)+1≤primeCount (SupportedPrimeCylinder.cutoff N q) := by
    exact_mod_cast h
  have hlog : (0 : ℝ)<Real.log 2 := Real.log_pos (by norm_num)
  calc
    _ = Real.exp (Real.log 2+(t*((ValuationPrimeCylinder.starts N q).card : ℝ)-
        (primeCount (SupportedPrimeCylinder.cutoff N q) : ℝ)*Real.log 2)) := by
      rw [Real.exp_add,Real.exp_log (by norm_num : (0 : ℝ)<2)]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      nlinarith

theorem positive_factor_two_example (t : ℝ) (ht : 0≤t) :
    2*Real.exp (t*((ValuationPrimeCylinder.starts 18 3).card : ℝ)-
      (primeCount (SupportedPrimeCylinder.cutoff 18 3) : ℝ)*Real.log 2)≤
        PositiveStarts.exponentialMoment (dyadicBlock 18) 2 t :=
  (factor_two_gain_of_rank_drop 18 3 strict_rank_gain_example t).trans
    (positive_exponential_card_lower (by decide : Nat.Prime 3) (by norm_num : 3≤18) t ht)

theorem total_factor_two_example (t : ℝ) (ht : 0≤t) :
    2*Real.exp (t*((ValuationPrimeCylinder.starts 18 3).card : ℝ)-
      (primeCount (SupportedPrimeCylinder.cutoff 18 3) : ℝ)*Real.log 2)≤
        PrimeRunCylinder.totalExponentialMoment 18 2 t :=
  (positive_factor_two_example t ht).trans (PrimeRunCylinder.positive_le_total 18 2 t ht)

theorem retained_parameters_example :
    ValuationPrimeCylinder.retainedParameters 18 3=Ico 7 12 := by
  ext u
  constructor
  · intro hu
    simpa [PrimeRunStarts.parameters] using (mem_filter.mp hu).1
  · intro hu
    apply mem_filter.mpr
    refine ⟨by simpa [PrimeRunStarts.parameters] using hu,?_⟩
    have hu' : 7≤u ∧ u<12 := mem_Ico.mp hu
    by_cases h9 : u=9
    · subst u
      change parityVec (3^2) 3=0
      rw [parityVec_pow_two,Finsupp.zero_apply]
    · apply OneNegativePrime.parity_zero_of_not_dvd
      rintro ⟨a,ha⟩
      omega

theorem retained_start_count_example : (ValuationPrimeCylinder.starts 18 3).card=5 := by
  rw [ValuationLayerCounts.valuation_starts_card 18 3 (by norm_num),retained_parameters_example]
  norm_num

theorem prime_count_example : primeCount (SupportedPrimeCylinder.cutoff 18 3)=11 := by
  decide +kernel

theorem retained_rank_example : retainedRank 18 3≤10 := by
  have h := strict_rank_gain_example
  rw [prime_count_example] at h
  omega

theorem positive_explicit_example (t : ℝ) (ht : 0≤t) :
    Real.exp (5*t-10*Real.log 2)≤PositiveStarts.exponentialMoment (dyadicBlock 18) 2 t := by
  have hr : (retainedRank 18 3 : ℝ)≤10 := by exact_mod_cast retained_rank_example
  have hlog : (0 : ℝ)≤Real.log 2 := Real.log_nonneg (by norm_num)
  apply (Real.exp_le_exp.mpr ?_).trans
    (positive_exponential_card_lower (by decide : Nat.Prime 3) (by norm_num : 3≤18) t ht)
  rw [retained_start_count_example]
  norm_num only [Nat.cast_ofNat]
  nlinarith

theorem total_explicit_example (t : ℝ) (ht : 0≤t) :
    Real.exp (5*t-10*Real.log 2)≤PrimeRunCylinder.totalExponentialMoment 18 2 t :=
  (positive_explicit_example t ht).trans (PrimeRunCylinder.positive_le_total 18 2 t ht)

end PaperP1.RankChargedPrimeCylinder
