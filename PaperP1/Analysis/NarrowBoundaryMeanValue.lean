module

public import PaperP1.Analysis.SupportedCoefficientSquareBudget
public import PaperP1.Analysis.NarrowPrimeBands
public import PaperP1.Analysis.NarrowRectangleWeight

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.NarrowBoundaryMeanValue
open Finset PaperP1 MeasureTheory
open scoped Classical

def constant : ℝ := Real.exp 1*(Real.sqrt Real.pi+8*Real.pi)

theorem constant_pos : 0 < constant := by unfold constant; positivity

theorem boundary_card (X H : ℕ) :
    ((NarrowRectangleWeight.boundary X H).card : ℝ) ≤
      3*(NarrowPrimeBands.growth H-1)*(X : ℝ)+2 := by
  let c := NarrowPrimeBands.growth H
  have hc : 1 ≤ c := NarrowPrimeBands.growth_one_le H
  have hX : (0 : ℝ) ≤ X := Nat.cast_nonneg X
  have hsub : NarrowRectangleWeight.boundary X H ⊆
      Ico X ⌈c*(X : ℝ)⌉₊ ∪ Ico (2*X) ⌈2*c*(X : ℝ)⌉₊ := by
    intro n hn
    obtain ⟨hn,ht⟩ := mem_filter.mp hn
    rcases ht with hl | hr
    · exact mem_union.mpr (Or.inl (mem_Ico.mpr ⟨(mem_Ico.mp hn).1,Nat.lt_ceil.mpr hl⟩))
    · exact mem_union.mpr (Or.inr (mem_Ico.mpr ⟨by exact_mod_cast hr.1,Nat.lt_ceil.mpr hr.2⟩))
  have hlow : X ≤ ⌈c*(X : ℝ)⌉₊ := by
    have hh : (X : ℝ) ≤ c*(X : ℝ) := by nlinarith
    exact_mod_cast hh.trans (Nat.le_ceil (c*(X : ℝ)))
  have hupp : 2*X ≤ ⌈2*c*(X : ℝ)⌉₊ := by
    have hh : ((2*X : ℕ) : ℝ) ≤ 2*c*(X : ℝ) := by push_cast; nlinarith
    exact_mod_cast hh.trans (Nat.le_ceil (2*c*(X : ℝ)))
  have hcard := (card_le_card hsub).trans (card_union_le _ _)
  have hcardR : ((NarrowRectangleWeight.boundary X H).card : ℝ) ≤
      ((⌈c*(X : ℝ)⌉₊ : ℕ) : ℝ)-(X : ℝ)+
      (((⌈2*c*(X : ℝ)⌉₊ : ℕ) : ℝ)-2*(X : ℝ)) := by
    have hcardN :
      (NarrowRectangleWeight.boundary X H).card ≤
        (⌈c*(X : ℝ)⌉₊-X)+(⌈2*c*(X : ℝ)⌉₊-2*X) := by
      simpa only [Nat.card_Ico] using hcard
    have hcardR : ((NarrowRectangleWeight.boundary X H).card : ℝ) ≤
        (((⌈c*(X : ℝ)⌉₊-X)+(⌈2*c*(X : ℝ)⌉₊-2*X) : ℕ) : ℝ) := by exact_mod_cast hcardN
    simpa only [Nat.cast_add,Nat.cast_sub hlow,Nat.cast_sub hupp,Nat.cast_mul,Nat.cast_ofNat] using hcardR
  have hceil1 := Nat.ceil_lt_add_one (show 0 ≤ c*(X : ℝ) by positivity)
  have hceil2 := Nat.ceil_lt_add_one (show 0 ≤ 2*c*(X : ℝ) by positivity)
  change _ ≤ 3*(c-1)*(X : ℝ)+2
  nlinarith only [hcardR,hceil1,hceil2]

theorem boundary_card_normalized (X H : ℕ) (hX : 0 < X) (hH : 2 ≤ H) :
    ((NarrowRectangleWeight.boundary X H).card : ℝ)/(X : ℝ) ≤ 6/(H : ℝ)+2/(X : ℝ) := by
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hh := boundary_card X H
  have he := NarrowPrimeBands.growth_error H hH
  apply (div_le_iff₀ hXR).mpr
  have hm := mul_le_mul_of_nonneg_right he (by positivity : (0 : ℝ) ≤ 3*(X : ℝ))
  calc
    _ ≤ 3*(NarrowPrimeBands.growth H-1)*(X : ℝ)+2 := hh
    _ = (NarrowPrimeBands.growth H-1)*(3*(X : ℝ))+2 := by ring
    _ ≤ (2/(H : ℝ))*(3*(X : ℝ))+2 := add_le_add hm (le_refl (2 : ℝ))
    _ = (6/(H : ℝ))*(X : ℝ)+2 := by ring
    _ = _ := by field_simp

theorem support_square_budget (N : ℕ) (hN : 0 < N) (S E : Finset ℕ)
    (hS : S ⊆ Ico N (4*N)) (hES : E ⊆ S) (a : ℕ → ℂ)
    (ha : ∀ n ∈ S, ‖a n‖ ≤ 1) (hz : ∀ n ∈ S, n ∉ E → a n=0) :
    (∑ n ∈ S, ‖a n/(n : ℂ)‖^2) ≤ (E.card : ℝ)/(N : ℝ)^2 := by
  have he : (∑ n ∈ E, ‖a n/(n : ℂ)‖^2)=∑ n ∈ S, ‖a n/(n : ℂ)‖^2 := by
    apply sum_subset hES
    intro n hn hnot
    rw [hz n hn hnot]
    simp
  rw [← he]
  calc
    _ ≤ ∑ _n ∈ E, 1/(N : ℝ)^2 := sum_le_sum (fun n hn ↦
      SupportedCoefficientSquareBudget.term_bound N n hN (mem_Ico.mp (hS (hES hn))).1 (a n) (ha n (hES hn)))
    _ = _ := by simp [div_eq_mul_inv]

theorem supported_uniform_bound (N : ℕ) (hN : 0 < N) (S E : Finset ℕ)
    (hS : S ⊆ Ico N (4*N)) (hES : E ⊆ S) (a : ℕ → ℂ)
    (ha : ∀ n ∈ S, ‖a n‖ ≤ 1) (hz : ∀ n ∈ S, n ∉ E → a n=0)
    (T : ℝ) (hT : 0 < T) (hTN : T ≤ N) :
    (∫ t in -T..T, ‖DirichletPolynomialMeanValue.value S a t‖^2) ≤
      constant*((E.card : ℝ)/(N : ℝ)) := by
  have hh := DirichletPolynomialMeanValue.logarithmic_interval_bound S (fun n ↦ a n/(n : ℂ)) (4*N)
    (by omega) (by
      intro n hn
      have hm := mem_Ico.mp (hS hn)
      omega) T hT
  change (∫ t in -T..T, ‖DirichletPolynomialMeanValue.value S a t‖^2) ≤ _ at hh
  have hb := support_square_budget N hN S E hS hES a ha hz
  have hc : Real.exp 1*(Real.sqrt Real.pi*T+2*Real.pi*((4*N : ℕ) : ℝ)) ≤ constant*(N : ℝ) := by
    unfold constant
    push_cast
    have hm := mul_le_mul_of_nonneg_left hTN (Real.sqrt_nonneg Real.pi)
    have he := mul_le_mul_of_nonneg_left
      (add_le_add hm (le_refl (8*Real.pi*(N : ℝ)))) (Real.exp_pos 1).le
    nlinarith only [he]
  calc
    _ ≤ Real.exp 1*(Real.sqrt Real.pi*T+2*Real.pi*((4*N : ℕ) : ℝ))*(∑ n ∈ S, ‖a n/(n : ℂ)‖^2) := hh
    _ ≤ constant*(N : ℝ)*((E.card : ℝ)/(N : ℝ)^2) := mul_le_mul hc hb
      (sum_nonneg (fun n hn ↦ sq_nonneg _)) (by unfold constant; positivity)
    _ = _ := by field_simp
end PaperP1.NarrowBoundaryMeanValue
