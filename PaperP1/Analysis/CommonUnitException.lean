module

public import PaperP1.Analysis.SlowPrimeDiscrete
public import PaperP1.Analysis.PrimeUnitMean
public import PaperP1.Analysis.RealPretentiousDistance
set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.CommonUnitException
open Finset Nat MeasureTheory PaperP1 Filter
open scoped Classical

def common (N : ℕ) (t : ℝ) : ℂ :=
  DirichletPolynomialMeanValue.value (SlowPrimeBandSieve.primes N) (fun _ ↦ 1) (2*t)

theorem common_continuous (N : ℕ) : Continuous (common N) :=
  (GaussianExponentialSums.polynomial_continuous _ _ _).comp (continuous_const.mul continuous_id)

def maxPoint (N K j : ℕ) : ℝ :=
  Classical.choose (PrimeUnitMean.local_sup_attained (common N) (common_continuous N) ((j : ℝ)-(K : ℝ)))

theorem maxPoint_mem (N K j : ℕ) : maxPoint N K j ∈ Set.Icc ((j : ℝ)-(K : ℝ)-1/2) ((j : ℝ)-(K : ℝ)+1/2) :=
  (Classical.choose_spec (PrimeUnitMean.local_sup_attained (common N) (common_continuous N) ((j : ℝ)-(K : ℝ)))).1

theorem maxPoint_eq (N K j : ℕ) :
    PrimeUnitMean.localSquareSup (common N) ((j : ℝ)-(K : ℝ))=‖common N (maxPoint N K j)‖^2 :=
  (Classical.choose_spec (PrimeUnitMean.local_sup_attained (common N) (common_continuous N) ((j : ℝ)-(K : ℝ)))).2

def badUnits (N K : ℕ) : Finset ℕ :=
  (range (2*K+1)).filter (fun j ↦ (PrimeAvoidanceSieve.reciprocalMass (SlowPrimeBandSieve.primes N)/2)^2 ≤
    PrimeUnitMean.localSquareSup (common N) ((j : ℝ)-(K : ℝ)))

theorem sample_range (N K j : ℕ) (hj : j ∈ range (2*K+1)) :
    -((2 : ℝ)*(K : ℝ)+1) ≤ 2*maxPoint N K j ∧ 2*maxPoint N K j ≤ (2 : ℝ)*(K : ℝ)+1 := by
  have hmem := maxPoint_mem N K j
  have hjN : j ≤ 2*K := by have hh := mem_range.mp hj; omega
  have hjR : (j : ℝ) ≤ 2*(K : ℝ) := by exact_mod_cast hjN
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  constructor <;> linarith [hmem.1,hmem.2]

theorem sample_separated (N K j s : ℕ) (hpar : j%2=s%2) (hne : j ≠ s) :
    1 ≤ |2*maxPoint N K j-2*maxPoint N K s| := by
  have hj := maxPoint_mem N K j
  have hs := maxPoint_mem N K s
  by_cases hjs : j < s
  · have hh : j+2 ≤ s := by omega
    have hhR : (j : ℝ)+2 ≤ (s : ℝ) := by exact_mod_cast hh
    rw [abs_of_nonpos (by linarith [hj.2,hs.1] : 2*maxPoint N K j-2*maxPoint N K s ≤ 0)]
    linarith [hj.2,hs.1]
  · have hh : s+2 ≤ j := by omega
    have hhR : (s : ℝ)+2 ≤ (j : ℝ) := by exact_mod_cast hh
    rw [abs_of_nonneg (by linarith [hs.2,hj.1] : 0 ≤ 2*maxPoint N K j-2*maxPoint N K s)]
    linarith [hs.2,hj.1]

theorem sample_big (N K j : ℕ) (hj : j ∈ badUnits N K) :
    PrimeAvoidanceSieve.reciprocalMass (SlowPrimeBandSieve.primes N)/2 ≤
      ‖DirichletPolynomialMeanValue.value (SlowPrimeBandSieve.primes N) (fun _ ↦ 1) (2*maxPoint N K j)‖ := by
  have hH : 0 ≤ PrimeAvoidanceSieve.reciprocalMass (SlowPrimeBandSieve.primes N)/2 := by
    apply div_nonneg _ (by norm_num)
    exact sum_nonneg (fun p _ ↦ by positivity)
  apply (sq_le_sq₀ hH (norm_nonneg _)).mp
  exact (mem_filter.mp hj).2.trans_eq (maxPoint_eq N K j)

theorem off_bad_distance (N K j : ℕ) (hj : j ∈ range (2*K+1)) (hnot : j ∉ badUnits N K)
    (f : ℕ → ℝ) (hf : ∀ p ∈ SlowPrimeBandSieve.primes N, |f p| ≤ 1) (t : ℝ)
    (ht : t ∈ Set.Icc ((j : ℝ)-(K : ℝ)-1/2) ((j : ℝ)-(K : ℝ)+1/2)) :
    PrimeAvoidanceSieve.reciprocalMass (SlowPrimeBandSieve.primes N)/8 <
      RealPretentiousDistance.distance (SlowPrimeBandSieve.primes N) f t := by
  by_contra! hclose
  have hlarge := RealPretentiousDistance.real_close_implies_prime_large _ f t hf hclose
  have hH : 0 ≤ PrimeAvoidanceSieve.reciprocalMass (SlowPrimeBandSieve.primes N)/2 := by
    apply div_nonneg _ (by norm_num)
    exact sum_nonneg (fun p _ ↦ by positivity)
  have hsquare := pow_le_pow_left₀ hH hlarge 2
  have hsup := PrimeUnitMean.norm_sq_le_local_sup (common N) (common_continuous N) ((j : ℝ)-(K : ℝ)) t ht
  exact hnot (mem_filter.mpr ⟨hj,hsquare.trans hsup⟩)


theorem bad_units_card_small (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ K : ℕ, (SlowPrimeBandSieve.upper N)^3 ≤ (K : ℝ) →
      ((badUnits N K).card : ℝ) ≤ ε*(2*(K : ℝ)+1) := by
  obtain ⟨N₀,hN₀,hh⟩ := SlowPrimeDiscrete.slow_large_values_small_uniform (ι := ℕ) (ε/2) (by positivity)
  refine ⟨N₀,hN₀,?_⟩
  intro N hN K hK
  let R₀ := (badUnits N K).filter (fun j ↦ j%2=0)
  let R₁ := (badUnits N K).filter (fun j ↦ ¬j%2=0)
  have hT : (SlowPrimeBandSieve.upper N)^3 ≤ 2*(K : ℝ)+1 := hK.trans (by have hh := Nat.cast_nonneg (α := ℝ) K; linarith)
  have h₀ := hh N hN R₀ (fun j ↦ 2*maxPoint N K j) (2*(K : ℝ)+1) hT
    (fun j hj ↦ sample_range N K j (mem_filter.mp (mem_filter.mp hj).1).1) (by
      intro j hj s hs hne
      apply sample_separated N K j s _ hne
      exact (mem_filter.mp hj).2.trans (mem_filter.mp hs).2.symm)
    (fun j hj ↦ sample_big N K j (mem_filter.mp hj).1)
  have h₁ := hh N hN R₁ (fun j ↦ 2*maxPoint N K j) (2*(K : ℝ)+1) hT
    (fun j hj ↦ sample_range N K j (mem_filter.mp (mem_filter.mp hj).1).1) (by
      intro j hj s hs hne
      apply sample_separated N K j s _ hne
      have hj' := (mem_filter.mp hj).2
      have hs' := (mem_filter.mp hs).2
      omega)
    (fun j hj ↦ sample_big N K j (mem_filter.mp hj).1)
  have hc := card_filter_add_card_filter_not (s := badUnits N K) (fun j ↦ j%2=0)
  have hcard : ((badUnits N K).card : ℝ)=(R₀.card : ℝ)+(R₁.card : ℝ) := by exact_mod_cast hc.symm
  rw [hcard]
  linarith

theorem unit_repulsion_small_uniform (B ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ K : ℕ, (SlowPrimeBandSieve.upper N)^3 ≤ (K : ℝ) →
      ((badUnits N K).card : ℝ) ≤ ε*(2*(K : ℝ)+1) ∧
        ∀ j ∈ range (2*K+1), j ∉ badUnits N K → ∀ f : ℕ → ℝ,
          (∀ p ∈ SlowPrimeBandSieve.primes N, |f p| ≤ 1) → ∀ t : ℝ,
          t ∈ Set.Icc ((j : ℝ)-(K : ℝ)-1/2) ((j : ℝ)-(K : ℝ)+1/2) →
            B ≤ RealPretentiousDistance.distance (SlowPrimeBandSieve.primes N) f t := by
  obtain ⟨N₁,hN₁,hcard⟩ := bad_units_card_small ε hε
  obtain ⟨N₂,hN₂⟩ := eventually_atTop.mp
    (SlowPrimeBandSieve.reciprocal_mass_tendsto.eventually (eventually_ge_atTop (8*B)))
  refine ⟨max N₁ N₂,hN₁.trans (le_max_left _ _),?_⟩
  intro N hN K hK
  refine ⟨hcard N (by omega) K hK,?_⟩
  intro j hj hnot f hf t ht
  have hd := off_bad_distance N K j hj hnot f hf t ht
  have hmass := hN₂ N (by omega)
  linarith
end PaperP1.CommonUnitException
