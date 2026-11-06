module

public import PaperP1.Analysis.FixedEulerTruncation
public import PaperP1.Arithmetic.PrimeHarmonicWindow
public import PaperP1.Analysis.ReciprocalSquareTail
set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.FullEulerBound
open Finset Nat MeasureTheory PaperP1 Filter
open scoped Classical

def harmonicConstant : ℝ := 1/2+|Real.log (Real.log 2)|+2*PrimeLogMertens.budget/Real.log 2

def eulerConstant : ℝ := Real.exp (harmonicConstant+1)

theorem eulerConstant_pos : 0 < eulerConstant := Real.exp_pos _

theorem harmonic_split (X : ℕ) (hX : 2 ≤ X) :
    PrimeAvoidanceSieve.reciprocalMass (FixedEulerTruncation.primes X)=
      1/2+PrimeHarmonicWindow.harmonic 2 (X : ℝ) := by
  have hset : FixedEulerTruncation.primes X=insert 2 ((Ioc 2 X).filter Nat.Prime) := by
    ext p
    simp only [FixedEulerTruncation.primes,mem_filter,mem_Icc,mem_insert,mem_Ioc]
    constructor
    · rintro ⟨hp,hprime⟩
      by_cases he : p=2
      · exact Or.inl he
      · exact Or.inr ⟨⟨by have hh := hprime.two_le; omega,hp.2⟩,hprime⟩
    · rintro (rfl | ⟨hp,hprime⟩)
      · exact ⟨⟨by omega,hX⟩,by decide⟩
      · exact ⟨⟨by omega,hp.2⟩,hprime⟩
  have hnot : 2 ∉ (Ioc 2 X).filter Nat.Prime := by simp
  have he : PrimeHarmonicWindow.harmonic 2 (X : ℝ)=∑ p ∈ (Ioc 2 X).filter Nat.Prime, 1/(p : ℝ) := by
    norm_num [PrimeHarmonicWindow.harmonic]
  rw [PrimeAvoidanceSieve.reciprocalMass,hset,sum_insert hnot,he]
  norm_num

theorem harmonic_upper (X : ℕ) (hX : 2 ≤ X) :
    PrimeAvoidanceSieve.reciprocalMass (FixedEulerTruncation.primes X) ≤ Real.log (Real.log (X : ℝ))+harmonicConstant := by
  have hw := PrimeHarmonicWindow.finite_window_bound 2 (X : ℝ) (by norm_num) (by exact_mod_cast hX)
  have hh := (abs_le.mp hw).2
  rw [harmonic_split X hX]
  dsimp only [harmonicConstant]
  linarith [neg_le_abs (Real.log (Real.log 2))]

theorem prime_square_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (∑ p ∈ P, 1/(p : ℝ)^2) ≤ 1 := by
  have hh := ReciprocalSquareTail.finite_bound 2 (by norm_num) P (fun p hp ↦ by exact_mod_cast (hP p hp).two_le)
  norm_num at hh
  simpa only [one_div] using hh

theorem distance_mono (A B : Finset ℕ) (hAB : A ⊆ B) (f : ℕ → ℝ)
    (hf : ∀ p ∈ B, |f p| ≤ 1) (t : ℝ) :
    RealPretentiousDistance.distance A f t ≤ RealPretentiousDistance.distance B f t := by
  exact sum_le_sum_of_subset_of_nonneg hAB (fun p hp _ ↦
    div_nonneg (RealPretentiousDistance.point_nonneg (f p) (t*Real.log p) (hf p hp)) (Nat.cast_nonneg p))

theorem euler_bound (X : ℕ) (hX : 2 ≤ X) (f : ℕ → ℝ)
    (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1) (t : ℝ) :
    ‖RealPrimeEulerBound.product (FixedEulerTruncation.primes X) f t‖ ≤
      eulerConstant*Real.log (X : ℝ)*Real.exp (-RealPretentiousDistance.distance (FixedEulerTruncation.primes X) f t) := by
  have hP := FixedEulerTruncation.primes_prime X
  have hsum := harmonic_upper X hX
  have hsquare := prime_square_bound (FixedEulerTruncation.primes X) hP
  have hh := RealPrimeEulerBound.norm_product_bound (FixedEulerTruncation.primes X) hP f (fun p hp ↦ hf p (hP p hp)) t
  have hlog : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  calc
    _ ≤ Real.exp (Real.log (Real.log (X : ℝ))+harmonicConstant-
        RealPretentiousDistance.distance (FixedEulerTruncation.primes X) f t+1) :=
      hh.trans (Real.exp_le_exp.mpr (by linarith))
    _ = _ := by
      rw [show Real.log (Real.log (X : ℝ))+harmonicConstant-
          RealPretentiousDistance.distance (FixedEulerTruncation.primes X) f t+1=
          (harmonicConstant+1)+Real.log (Real.log (X : ℝ))+
            (-RealPretentiousDistance.distance (FixedEulerTruncation.primes X) f t) by ring,
        Real.exp_add,Real.exp_add,Real.exp_log hlog]
      rfl

theorem euler_subset_bound (X : ℕ) (hX : 2 ≤ X) (S : Finset ℕ)
    (hS : S ⊆ FixedEulerTruncation.primes X) (f : ℕ → ℝ)
    (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1) (t : ℝ) :
    ‖RealPrimeEulerBound.product (FixedEulerTruncation.primes X) f t‖ ≤
      eulerConstant*Real.log (X : ℝ)*Real.exp (-RealPretentiousDistance.distance S f t) := by
  have hd := distance_mono S (FixedEulerTruncation.primes X) hS f
    (fun p hp ↦ hf p (FixedEulerTruncation.primes_prime X p hp)) t
  have hlog : 0 ≤ Real.log (X : ℝ) := Real.log_natCast_nonneg X
  exact (euler_bound X hX f hf t).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
    (mul_nonneg eulerConstant_pos.le hlog))

theorem global_bound (X : ℕ) (hX : 2 ≤ X) (f : ℕ → ℝ)
    (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1) (t : ℝ) :
    ‖RealPrimeEulerBound.product (FixedEulerTruncation.primes X) f t‖ ≤ eulerConstant*Real.log (X : ℝ) := by
  have hh := euler_subset_bound X hX ∅ (empty_subset _) f hf t
  simpa only [RealPretentiousDistance.distance,sum_empty,neg_zero,Real.exp_zero,mul_one] using hh

theorem slow_subset (N X : ℕ) (hN : 1 ≤ N) (hNX : N ≤ X) :
    SlowPrimeBandSieve.primes N ⊆ FixedEulerTruncation.primes X := by
  intro p hp
  have hh := mem_filter.mp hp
  have hupper : (p : ℝ) ≤ SlowPrimeBandSieve.upper N :=
    (by exact_mod_cast (mem_Ioc.mp hh.1).2 : (p : ℝ) ≤ ⌊SlowPrimeBandSieve.upper N⌋₊).trans
      (Nat.floor_le (Real.log_natCast_nonneg N))
  have hlog := Real.log_le_sub_one_of_pos (by exact_mod_cast (by omega : 0 < N) : (0 : ℝ) < N)
  have hpN : p ≤ N := by dsimp only [SlowPrimeBandSieve.upper] at hupper; exact_mod_cast (by linarith : (p : ℝ) ≤ N)
  exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hh.2.one_le,hpN.trans hNX⟩,hh.2⟩


theorem small_of_distance (X : ℕ) (hX : 2 ≤ X) (S : Finset ℕ)
    (hS : S ⊆ FixedEulerTruncation.primes X) (f : ℕ → ℝ)
    (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1) (t δ : ℝ) (hδ : 0 < δ)
    (hD : harmonicConstant+1-Real.log δ ≤ RealPretentiousDistance.distance S f t) :
    ‖RealPrimeEulerBound.product (FixedEulerTruncation.primes X) f t‖ ≤ δ*Real.log (X : ℝ) := by
  calc
    _ ≤ eulerConstant*Real.log (X : ℝ)*Real.exp (-RealPretentiousDistance.distance S f t) :=
      euler_subset_bound X hX S hS f hf t
    _ = Real.log (X : ℝ)*Real.exp (harmonicConstant+1-RealPretentiousDistance.distance S f t) := by
      rw [sub_eq_add_neg,Real.exp_add]
      dsimp only [eulerConstant]
      ring
    _ ≤ Real.log (X : ℝ)*Real.exp (Real.log δ) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (Real.log_natCast_nonneg X)
    _ = _ := by rw [Real.exp_log hδ]; ring

theorem common_off_exception (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, 2 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ T : ℝ, SlowPrimeBandSieve.upper X ≤ T →
      ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Set.Ioc (-T) T ∧ volume.real E ≤ ε*T ∧
        ∀ t ∈ Set.Ioc (-T) T, t ∉ E → ∀ f : ℕ → ℝ,
          (∀ p : ℕ, p.Prime → |f p| ≤ 1) →
            ‖RealPrimeEulerBound.product (FixedEulerTruncation.primes X) f t‖ ≤ δ*Real.log (X : ℝ) := by
  obtain ⟨X₁,hX₁,hh⟩ := CommonPrimeFrequencyException.common_repulsion_uniform (harmonicConstant+1-Real.log δ) ε hε
  refine ⟨max X₁ 2,le_max_right _ _,?_⟩
  intro X hX T hT
  obtain ⟨E,hE,hsub,hm,hoff⟩ := hh X (by omega) T hT
  refine ⟨E,hE,hsub,hm,?_⟩
  intro t ht hnot f hf
  apply small_of_distance X (by omega) (SlowPrimeBandSieve.primes X) (slow_subset X X (by omega) le_rfl) f hf t δ hδ
  exact hoff t ht hnot f (fun p hp ↦ hf p (mem_filter.mp hp).2)

def normalized (X : ℕ) (f : ℕ → ℝ) (t : ℝ) : ℝ :=
  ‖RealPrimeEulerBound.product (FixedEulerTruncation.primes X) f t‖/Real.log (X : ℝ)

theorem normalized_continuous (X : ℕ) (f : ℕ → ℝ)
    (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1) : Continuous (normalized X f) := by
  exact (RealPrimeEulerBound.product_continuous (FixedEulerTruncation.primes X) (FixedEulerTruncation.primes_prime X)
    f (fun p hp ↦ hf p (FixedEulerTruncation.primes_prime X p hp))).norm.div_const _

theorem normalized_nonneg (X : ℕ) (f : ℕ → ℝ) (t : ℝ) : 0 ≤ normalized X f t :=
  div_nonneg (norm_nonneg _) (Real.log_natCast_nonneg X)

theorem normalized_bound (X : ℕ) (hX : 2 ≤ X) (f : ℕ → ℝ)
    (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1) (t : ℝ) : normalized X f t ≤ eulerConstant := by
  have hlog : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  exact (div_le_iff₀ hlog).mpr (global_bound X hX f hf t)



theorem normalized_square_mean_small (η : ℝ) (hη : 0 < η) :
    ∃ X₀ : ℕ, 2 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ T : ℝ, SlowPrimeBandSieve.upper X ≤ T →
      ∀ f : ℕ → ℝ, (∀ p : ℕ, p.Prime → |f p| ≤ 1) →
        (∫ t in -T..T, (normalized X f t)^2) ≤ η*T := by
  let δ : ℝ := Real.sqrt η/4
  let ε : ℝ := η/(4*eulerConstant^2)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hε : 0 < ε := by have hc := eulerConstant_pos; dsimp only [ε]; positivity
  obtain ⟨X₀,hX₀,hh⟩ := common_off_exception δ ε hδ hε
  refine ⟨X₀,hX₀,?_⟩
  intro X hX T hT f hf
  have hX2 := hX₀.trans hX
  have hlog : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  have hTp : 0 < T := lt_of_lt_of_le hlog hT
  obtain ⟨E,hE,hsub,hm,hoff⟩ := hh X hX T hT
  have hb := ExceptionalSquareIntegral.square_integral_budget (normalized X f) (normalized_continuous X f hf)
    T eulerConstant δ hTp E hE hsub (fun t _ ↦ normalized_nonneg X f t)
    (fun t _ ↦ normalized_bound X hX2 f hf t) (by
      intro t ht hnot
      exact (div_le_iff₀ hlog).mpr (hoff t ht hnot f hf))
  have hs : δ^2=η/16 := by dsimp only [δ]; rw [div_pow,Real.sq_sqrt hη.le]; norm_num
  have hc : eulerConstant^2*ε=η/4 := by dsimp only [ε]; field_simp [eulerConstant_pos.ne']
  have he := mul_le_mul_of_nonneg_left hm (sq_nonneg eulerConstant)
  have heq : eulerConstant^2*(ε*T)=η/4*T := by rw [← mul_assoc,hc]
  rw [heq] at he
  rw [hs] at hb
  nlinarith
end PaperP1.FullEulerBound
