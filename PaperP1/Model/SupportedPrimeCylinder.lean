module

public import PaperP1.Model.OneSidedPrimeCylinder
public import PaperP1.Coding.LocalRigidityCode

/-! # Charge only the prime signs used by the retained starts
The one-sided retained starts end before 2q floor(N/q), which is at most
2N. Their restricted count is determined by those prime signs, even
though the full count uses a larger sufficient cutoff. Integrability
and monotonicity connect the smaller cylinder to the actual full moments.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace PaperP1.SupportedPrimeCylinder

open Finset MeasureTheory PaperP1.Arithmetic PaperP1.Model PaperP1.Algebra
  PaperP1.Probability PaperP1.Model.InfiniteRademacher PaperP1.LocalDefectBound
  PaperP1.Probability.InfiniteCylinderTransfer PaperP1.Probability.CylinderExpectations

local instance supportedCylinderMeasurableF₂ : MeasurableSpace F₂ := ⊤

def cutoff (N q : ℕ) : ℕ := 2*q*(N/q)

theorem cutoff_le_two_mul (N q : ℕ) : cutoff N q≤2*N := by
  have h := Nat.div_mul_le_self N q
  unfold cutoff
  nlinarith

theorem cylinder_integrable (M : ℕ) (f : SampleSpace M → ℝ) :
    Integrable (fun ω ↦ f (restrictToFinite M ω)) infiniteRademacherMeasure :=
  (integrable_finite_function (infiniteRademacherMeasure.map (restrictToFinite M)) f).comp_measurable
    (measurable_restrictToFinite M)

theorem positive_integrable (G : Finset ℕ) (L : ℕ) (t : ℝ) :
    Integrable (fun ω ↦ Real.exp (t*(PositiveStarts.infiniteCount G L ω : ℝ)))
      infiniteRademacherMeasure := by
  let M := G.sup fun x ↦ x+L
  have hcut : ∀ x ∈ G, x+L≤M := fun x hx ↦ le_sup (f:=fun x ↦ x+L) hx
  let f : SampleSpace M → ℝ := fun σ ↦
    Real.exp (t*(indicatorCount G (fun x ↦ PositiveStarts.indicator x L) σ : ℝ))
  have h := cylinder_integrable M f
  have heq : (fun ω ↦ Real.exp (t*(PositiveStarts.infiniteCount G L ω : ℝ)))=
      (fun ω ↦ f (restrictToFinite M ω)) := by
    funext ω
    dsimp [f]
    rw [PositiveStarts.count_restrict G L M hcut]
  rw [heq]
  exact h

theorem positive_moment_mono {G H : Finset ℕ} (hGH : G⊆H) (L : ℕ)
    (t : ℝ) (ht : 0≤t) :
    PositiveStarts.exponentialMoment G L t≤PositiveStarts.exponentialMoment H L t := by
  apply integral_mono (positive_integrable G L t) (positive_integrable H L t)
  intro ω
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ ht
  have h : PositiveStarts.infiniteCount G L ω≤PositiveStarts.infiniteCount H L ω :=
    sum_le_sum_of_subset hGH
  exact_mod_cast h

theorem positive_moment_eq_finite {M L : ℕ} {G : Finset ℕ}
    (hcut : ∀ x ∈ G, x+L≤M) (t : ℝ) :
    PositiveStarts.exponentialMoment G L t=
      finiteExpectation (cylinderProbability M).weight (fun σ ↦
        Real.exp (t*(indicatorCount G (fun x ↦ PositiveStarts.indicator x L) σ : ℝ))) := by
  unfold PositiveStarts.exponentialMoment
  have heq : (fun ω ↦ Real.exp (t*(PositiveStarts.infiniteCount G L ω : ℝ)))=
      (fun ω ↦ Real.exp (t*(indicatorCount G (fun x ↦ PositiveStarts.indicator x L)
        (restrictToFinite M ω) : ℝ))) := by
    funext ω
    rw [PositiveStarts.count_restrict G L M hcut]
  rw [heq]
  exact infiniteCylinder_integral M (fun σ : SampleSpace M ↦
    Real.exp (t*(indicatorCount G (fun x ↦ PositiveStarts.indicator x L) σ : ℝ)))

theorem retained_starts_cutoff {N q : ℕ} (hq : 2≤q) (hqN : q≤N) :
    ∀ x ∈ OneSidedPrimeCylinder.starts N q, x+(q-1)≤cutoff N q := by
  intro x hx
  obtain ⟨u, hu, _hnot, rfl⟩ := (OneSidedPrimeCylinder.mem_starts N q x).mp hx
  have hqpos : 0<q := by omega
  have hdiv : 1≤N/q := (Nat.le_div_iff_mul_le hqpos).mpr (by simpa only [one_mul] using hqN)
  obtain ⟨_hlo,hhi⟩ := mem_Ico.mp hu
  have hu : u+1≤2*(N/q) := by omega
  have hmul := Nat.mul_le_mul_left q hu
  have hsub : q-1+1=q := by omega
  unfold cutoff
  nlinarith

theorem positive_count_on_retained_sample {M N : ℕ} (q : PrimeUpTo M) :
    (OneSidedPrimeCylinder.starts N q.val.val).card≤
      indicatorCount (OneSidedPrimeCylinder.starts N q.val.val)
        (fun x ↦ PositiveStarts.indicator x (q.val.val-1)) (OneNegativePrime.sample q) := by
  rw [← card_activeSites]
  apply card_le_card
  intro x hx
  obtain ⟨u, _hu, hnot, heq⟩ := (OneSidedPrimeCylinder.mem_starts N q.val.val x).mp hx
  have hstart := OneSidedPrimeCylinder.positive_start q u hnot
  apply mem_filter.mpr
  refine ⟨hx, ?_⟩
  rw [← heq]
  simp only [PositiveStarts.indicator, Bool.and_eq_true, decide_eq_true_eq, startIndicator_eq_true_iff]
  exact hstart

theorem positive_exponential_card_lower {N q : ℕ} (hq : Nat.Prime q) (hqN : q≤N)
    (t : ℝ) (ht : 0≤t) :
    Real.exp (t*((OneSidedPrimeCylinder.starts N q).card : ℝ)-
      (primeCount (cutoff N q) : ℝ)*Real.log 2)≤
        PositiveStarts.exponentialMoment (dyadicBlock N) (q-1) t := by
  let M := cutoff N q
  let p : PrimeUpTo M := ⟨⟨q, by
    have hdiv : 1≤N/q := (Nat.le_div_iff_mul_le hq.pos).mpr (by simpa only [one_mul] using hqN)
    have hmul := Nat.mul_le_mul_left (2*q) hdiv
    dsimp [M,cutoff]
    nlinarith⟩, hq⟩
  let σ := OneNegativePrime.sample p
  let G := OneSidedPrimeCylinder.starts N q
  have hcount := positive_count_on_retained_sample (N:=N) p
  have hcountR : (G.card : ℝ)≤
      (indicatorCount G (fun x ↦ PositiveStarts.indicator x (q-1)) σ : ℝ) := by
    exact_mod_cast hcount
  have hatom := PrimeRunCylinder.finiteExpectation_ge_atom (cylinderProbability M)
    (fun σ ↦ Real.exp (t*(indicatorCount G (fun x ↦ PositiveStarts.indicator x (q-1)) σ : ℝ)))
      (fun _ ↦ (Real.exp_pos _).le) σ
  have hrestricted : Real.exp (t*(G.card : ℝ)-(primeCount M : ℝ)*Real.log 2)≤
      PositiveStarts.exponentialMoment G (q-1) t := by
    rw [positive_moment_eq_finite (retained_starts_cutoff hq.two_le hqN)]
    calc
      _ = (cylinderProbability M).weight σ*Real.exp (t*(G.card : ℝ)) := by
        rw [PrimeCylinderSize.atom_weight, Real.exp_sub, Real.exp_nat_mul,
          Real.exp_log (by norm_num : (0 : ℝ)<2)]
        ring
      _ ≤ (cylinderProbability M).weight σ*Real.exp
          (t*(indicatorCount G (fun x ↦ PositiveStarts.indicator x (q-1)) σ : ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hcountR ht))
          ((cylinderProbability M).weight_nonneg σ)
      _ ≤ _ := hatom
  exact hrestricted.trans (positive_moment_mono
    (OneSidedPrimeCylinder.starts_subset_interval hq.two_le hqN) (q-1) t ht)

theorem positive_exponential_lower {N q : ℕ} (hq : Nat.Prime q) (hqN : q≤N)
    (t : ℝ) (ht : 0≤t) :
    Real.exp (t*((N : ℝ)/q-(N : ℝ)/(q : ℝ)^2-3)-
      (primeCount (cutoff N q) : ℝ)*Real.log 2)≤
        PositiveStarts.exponentialMoment (dyadicBlock N) (q-1) t :=
  (Real.exp_le_exp.mpr (sub_le_sub_right
    (mul_le_mul_of_nonneg_left (OneSidedPrimeCylinder.starts_card_lower hq.two_le hqN) ht) _)).trans
      (positive_exponential_card_lower hq hqN t ht)

theorem total_exponential_lower {N q : ℕ} (hq : Nat.Prime q) (hqN : q≤N)
    (t : ℝ) (ht : 0≤t) :
    Real.exp (t*((N : ℝ)/q-(N : ℝ)/(q : ℝ)^2-3)-
      (primeCount (cutoff N q) : ℝ)*Real.log 2)≤
        PrimeRunCylinder.totalExponentialMoment N (q-1) t :=
  (positive_exponential_lower hq hqN t ht).trans (PrimeRunCylinder.positive_le_total N (q-1) t ht)

theorem prime_charge_le_two_mul (N q : ℕ) :
    primeCount (cutoff N q)≤primeCount (2*N) := by
  simp only [LocalRigidityCode.primeCount_eq_primeCounting]
  exact Nat.monotone_primeCounting (cutoff_le_two_mul N q)

theorem prime_charge_never_larger (N q : ℕ) :
    primeCount (cutoff N q)≤primeCount (dyadicCutoff N (q-1)) := by
  apply (prime_charge_le_two_mul N q).trans
  simp only [LocalRigidityCode.primeCount_eq_primeCounting]
  exact Nat.monotone_primeCounting (by unfold dyadicCutoff; omega)

theorem dyadic_positive_exponential_lower {N q : ℕ} (hq : Nat.Prime q) (hqN : q≤N)
    (t : ℝ) (ht : 0≤t) :
    Real.exp (t*((N : ℝ)/q-(N : ℝ)/(q : ℝ)^2-3)-
      (primeCount (2*N) : ℝ)*Real.log 2)≤
        PositiveStarts.exponentialMoment (dyadicBlock N) (q-1) t := by
  have hcount : (primeCount (cutoff N q) : ℝ)≤primeCount (2*N) := by
    exact_mod_cast prime_charge_le_two_mul N q
  have hcharge := mul_le_mul_of_nonneg_right hcount (Real.log_nonneg (by norm_num : (1 : ℝ)≤2))
  exact (Real.exp_le_exp.mpr (sub_le_sub_left hcharge _)).trans
    (positive_exponential_lower hq hqN t ht)

theorem dyadic_total_exponential_lower {N q : ℕ} (hq : Nat.Prime q) (hqN : q≤N)
    (t : ℝ) (ht : 0≤t) :
    Real.exp (t*((N : ℝ)/q-(N : ℝ)/(q : ℝ)^2-3)-
      (primeCount (2*N) : ℝ)*Real.log 2)≤
        PrimeRunCylinder.totalExponentialMoment N (q-1) t :=
  (dyadic_positive_exponential_lower hq hqN t ht).trans
    (PrimeRunCylinder.positive_le_total N (q-1) t ht)

theorem strict_charge_reduction_on_original_scale :
    primeCount (cutoff (2^(7-1)) 7)<
      primeCount (dyadicCutoff (2^(7-1)) (7-1)) := by
  simp only [LocalRigidityCode.primeCount_eq_primeCounting, dyadicCutoff, cutoff]
  decide +kernel

theorem exact_prime_charges_on_original_scale :
    primeCount (cutoff (2^(7-1)) 7)=30 ∧ primeCount (2*(2^(7-1)))=31 ∧
      primeCount (dyadicCutoff (2^(7-1)) (7-1))=32 := by
  simp only [LocalRigidityCode.primeCount_eq_primeCounting, dyadicCutoff, cutoff]
  decide +kernel

theorem exponential_bound_gain_on_original_scale (b : ℝ) :
    Real.exp (b-(primeCount (cutoff (2^(7-1)) 7) : ℝ)*Real.log 2)=
      4*Real.exp (b-(primeCount (dyadicCutoff (2^(7-1)) (7-1)) : ℝ)*Real.log 2) := by
  obtain ⟨hnew, _hmid, hold⟩ := exact_prime_charges_on_original_scale
  rw [hnew,hold]
  norm_num only [Nat.cast_ofNat]
  have heq : b-(30 : ℝ)*Real.log 2=2*Real.log 2+(b-32*Real.log 2) := by ring
  have htwo : Real.exp (2*Real.log 2)=4 := by
    calc
      _ = Real.exp (Real.log 2)*Real.exp (Real.log 2) := by
        rw [← Real.exp_add]
        exact congrArg Real.exp (by ring)
      _ = _ := by rw [Real.exp_log (by norm_num : (0 : ℝ)<2)]; norm_num
  rw [heq,Real.exp_add,htwo]

end PaperP1.SupportedPrimeCylinder
