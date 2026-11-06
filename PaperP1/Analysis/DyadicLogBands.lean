module

public import PaperP1.Analysis.PrimeLogDiameter
public import PaperP1.Arithmetic.RealTripleConvolution

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.DyadicLogBands
open Finset Nat MeasureTheory PaperP1 Filter
open scoped Classical

theorem log_two_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)

theorem power_exists (X : ℕ) : ∃ K : ℕ, Real.log (X : ℝ) ≤ Real.log 2*(2 : ℝ)^K := by
  obtain ⟨K,hK⟩ := pow_unbounded_of_one_lt (Real.log (X : ℝ)/Real.log 2) (by norm_num : (1 : ℝ) < 2)
  refine ⟨K,?_⟩
  have hh := (div_le_iff₀ log_two_pos).mp hK.le
  simpa only [mul_comm] using hh

def exponent (X : ℕ) : ℕ := Nat.find (power_exists X)

def count (X : ℕ) : ℕ := exponent X+1

def scale (j : ℕ) : ℝ := Real.log 2*(2 : ℝ)^j

theorem exponent_cover (X : ℕ) : Real.log (X : ℝ) ≤ scale (exponent X) := Nat.find_spec (power_exists X)

theorem exponent_scale_upper (X : ℕ) (hX : 2 ≤ X) : scale (exponent X) ≤ 2*Real.log (X : ℝ) := by
  have hlog : Real.log (2 : ℝ) ≤ Real.log (X : ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hX)
  cases hK : exponent X with
  | zero => simp only [scale,pow_zero,mul_one]; linarith [log_two_pos]
  | succ k =>
    have hmin : ¬Real.log (X : ℝ) ≤ Real.log 2*(2 : ℝ)^k := Nat.find_min (power_exists X) (by change k < exponent X; omega)
    have hh := lt_of_not_ge hmin
    dsimp only [scale]
    rw [pow_succ]
    nlinarith

def index (X p : ℕ) : ℕ :=
  if h : Real.log 2 ≤ Real.log ((X : ℝ)/(p : ℝ)) ∧ Real.log ((X : ℝ)/(p : ℝ)) ≤ Real.log (X : ℝ) then
    Classical.choose (PrimeLogDiameter.dyadic_cover (Real.log 2) (Real.log ((X : ℝ)/(p : ℝ))) log_two_pos h.1 (exponent X)
      (h.2.trans (exponent_cover X))) else 0

def band (X : ℕ) (P : Finset ℕ) (j : ℕ) : Finset ℕ := P.filter (fun p ↦ index X p=j)

theorem index_spec (X p : ℕ)
    (h : Real.log 2 ≤ Real.log ((X : ℝ)/(p : ℝ)) ∧ Real.log ((X : ℝ)/(p : ℝ)) ≤ Real.log (X : ℝ)) :
    index X p ∈ range (count X) ∧ scale (index X p) ≤ Real.log ((X : ℝ)/(p : ℝ)) ∧
      Real.log ((X : ℝ)/(p : ℝ)) ≤ 2*scale (index X p) := by
  rw [index,dite_eq_left h]
  exact Classical.choose_spec (PrimeLogDiameter.dyadic_cover (Real.log 2) (Real.log ((X : ℝ)/(p : ℝ))) log_two_pos h.1
    (exponent X) (h.2.trans (exponent_cover X)))

theorem level_bounds (X p : ℕ) (hX : 2 ≤ X) (hp : p.Prime) (hXp : 2*p ≤ X) :
    Real.log 2 ≤ Real.log ((X : ℝ)/(p : ℝ)) ∧ Real.log ((X : ℝ)/(p : ℝ)) ≤ Real.log (X : ℝ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hXR : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  constructor
  · apply Real.log_le_log (by norm_num)
    apply (le_div_iff₀ hpR).mpr
    exact_mod_cast hXp
  · apply Real.log_le_log (div_pos hXR hpR)
    apply (div_le_iff₀ hpR).mpr
    nlinarith


theorem scale_pos (j : ℕ) : 0 < scale j := by
  dsimp only [scale]
  exact mul_pos log_two_pos (by positivity)

theorem scale_ge_log_two (j : ℕ) : Real.log 2 ≤ scale j := by
  have hh : (1 : ℝ) ≤ (2 : ℝ)^j := one_le_pow₀ (by norm_num)
  have hm := mul_le_mul_of_nonneg_left hh log_two_pos.le
  simpa only [scale,mul_one] using hm

theorem band_subset (X : ℕ) (P : Finset ℕ) (j : ℕ) : band X P j ⊆ P := filter_subset _ _

theorem band_bounds (X : ℕ) (hX : 2 ≤ X) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ 2*p ≤ X)
    (j p : ℕ) (hp : p ∈ band X P j) :
    scale j ≤ Real.log ((X : ℝ)/(p : ℝ)) ∧ Real.log ((X : ℝ)/(p : ℝ)) ≤ 2*scale j := by
  have hp' := mem_filter.mp hp
  have hh := (index_spec X p (level_bounds X p hX (hP p hp'.1).1 (hP p hp'.1).2)).2
  simpa only [hp'.2] using hh

theorem index_mem (X : ℕ) (hX : 2 ≤ X) (p : ℕ) (hp : p.Prime) (hXp : 2*p ≤ X) : index X p ∈ range (count X) :=
  (index_spec X p (level_bounds X p hX hp hXp)).1

theorem band_disjoint (X : ℕ) (P : Finset ℕ) (j k : ℕ) (hjk : j ≠ k) : Disjoint (band X P j) (band X P k) := by
  apply disjoint_left.mpr
  intro p hpj hpk
  exact hjk ((mem_filter.mp hpj).2.symm.trans (mem_filter.mp hpk).2)

theorem triple_partition (X : ℕ) (hX : 2 ≤ X) (g : ℕ →* ℂ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ 2*p ≤ X) :
    RealTripleConvolution.triple g X P=∑ j ∈ range (count X), RealTripleConvolution.triple g X (band X P j) := by
  have hmap : ∀ p ∈ P, index X p ∈ range (count X) := fun p hp ↦ index_mem X hX p (hP p hp).1 (hP p hp).2
  dsimp only [RealTripleConvolution.triple,band]
  symm
  exact sum_fiberwise_of_maps_to hmap (fun p ↦
    ((Real.log (p : ℝ)/Real.log ((X : ℝ)/(p : ℝ)) : ℝ) : ℂ)*g p*MultiplicativeLogConvolution.prime g (X/p))
end PaperP1.DyadicLogBands
