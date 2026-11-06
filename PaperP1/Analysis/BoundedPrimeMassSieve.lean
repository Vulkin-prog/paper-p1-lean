module

public import PaperP1.Arithmetic.PrimeAvoidanceSieve
public import PaperP1.Analysis.FlexiblePrimeBandSieve

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.BoundedPrimeMassSieve
open Finset Filter PaperP1 PrimeAvoidanceSieve
open scoped Classical

theorem normalized_avoidance_bound (N : ℕ) (hN : 0 < N) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (M : ℝ) (hM : 0 < M) (hMass : M ≤ reciprocalMass P) :
    ((avoiding P (2*N)).card : ℝ)/(N : ℝ) ≤
      2/M+(((P.card : ℝ)^2/(N : ℝ))/M^2) := by
  have hNP : (0 : ℝ) < N := by exact_mod_cast hN
  have hHP : 0 < reciprocalMass P := hM.trans_le hMass
  have hh := div_le_div_of_nonneg_right (avoidance_card P hP (2*N) hHP) (Nat.cast_nonneg N)
  have he : (((2*N : ℕ) : ℝ)/reciprocalMass P+(P.card : ℝ)^2/(reciprocalMass P)^2)/(N : ℝ)=
      2/reciprocalMass P+((P.card : ℝ)^2/(N : ℝ))/(reciprocalMass P)^2 := by
    push_cast
    field_simp [hNP.ne',hHP.ne']
  rw [he] at hh
  apply hh.trans
  exact add_le_add
    (div_le_div_of_nonneg_left (by norm_num) hM hMass)
    (div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hM) (pow_le_pow_left₀ hM.le hMass 2))

theorem avoidance_eventually_bound (P : ℕ → Finset ℕ)
    (hP : ∀ N p, p ∈ P N → p.Prime) (M : ℝ) (hM : 0 < M)
    (hMass : ∀ᶠ N : ℕ in atTop, M ≤ reciprocalMass (P N))
    (hCard : Tendsto (fun N : ℕ ↦ ((P N).card : ℝ)^2/(N : ℝ)) atTop (nhds 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ((avoiding (P N) (2*N)).card : ℝ)/(N : ℝ) ≤ 2/M+ε := by
  have hEnvelope : Tendsto (fun N : ℕ ↦ 2/M+(((P N).card : ℝ)^2/(N : ℝ))/M^2) atTop (nhds (2/M)) := by
    simpa only [zero_div,add_zero] using tendsto_const_nhds.add (hCard.div_const (M^2))
  have hSmall := (tendsto_order.mp hEnvelope).2 (2/M+ε) (by linarith only [hε])
  filter_upwards [hMass,eventually_ge_atTop 1,hSmall] with N hMassN hN hBound
  exact (normalized_avoidance_bound N (by omega) (P N) (hP N) M hM hMassN).trans hBound.le

theorem excluded_eventually_bound (P S : ℕ → Finset ℕ)
    (hP : ∀ N p, p ∈ P N → p.Prime) (M : ℝ) (hM : 0 < M)
    (hMass : ∀ᶠ N : ℕ in atTop, M ≤ reciprocalMass (P N))
    (hCard : Tendsto (fun N : ℕ ↦ ((P N).card : ℝ)^2/(N : ℝ)) atTop (nhds 0))
    (hSquare : Tendsto (fun N : ℕ ↦ ((S N).card : ℝ)/(N : ℝ)) atTop (nhds 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (((avoiding (P N) (2*N)) ∪ S N).card : ℝ)/(N : ℝ) ≤ 2/M+ε := by
  have hAvoid := avoidance_eventually_bound P hP M hM hMass hCard (ε/2) (by positivity)
  have hSq := (tendsto_order.mp hSquare).2 (ε/2) (by positivity)
  filter_upwards [hAvoid,hSq] with N hA hS
  have hUnion : (((avoiding (P N) (2*N)) ∪ S N).card : ℝ) ≤
      ((avoiding (P N) (2*N)).card : ℝ)+((S N).card : ℝ) := by
    exact_mod_cast card_union_le (avoiding (P N) (2*N)) (S N)
  have hh := div_le_div_of_nonneg_right hUnion (Nat.cast_nonneg N)
  rw [add_div] at hh
  linarith only [hh,hA,hS]
end PaperP1.BoundedPrimeMassSieve
