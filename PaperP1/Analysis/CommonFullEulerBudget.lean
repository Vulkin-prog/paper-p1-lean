module

public import PaperP1.Analysis.FullEulerBound
public import PaperP1.Analysis.CommonUnitException
public import PaperP1.Analysis.FullEulerEnvelope
public import PaperP1.Analysis.ShiftedExceptionWeight

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.CommonFullEulerBudget
open Finset Nat MeasureTheory PaperP1 Filter
open scoped Classical

theorem common_budget_small_uniform (η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ (M : ℕ) (T : ℝ), 1 ≤ T → (M : ℝ) ≤ T →
      (SlowPrimeBandSieve.upper N)^3 ≤ T →
      ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Set.Ioc (-T) T ∧ volume.real E ≤ ε*T ∧
        ∀ X ≥ N, ∀ f : ℕ → ℝ, (∀ p : ℕ, p.Prime → |f p| ≤ 1) →
          ∀ τ ∈ Set.Ioc (-T) T, τ ∉ E →
            PrimeUnitMean.frequencyBudget (fun t ↦ RealPrimeEulerBound.product (FixedEulerTruncation.primes X) f (t+τ)) M ≤
              η*(Real.log (X : ℝ))^2 := by
  let δ : ℝ := Real.sqrt (η/10)
  let V : ℝ := η/(2*FullEulerBound.eulerConstant^2)
  let ζ : ℝ := ε*V/70
  have hC := FullEulerBound.eulerConstant_pos
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hV : 0 < V := by dsimp only [V]; positivity
  have hζ : 0 < ζ := by dsimp only [ζ]; positivity
  have hδsq : δ^2=η/10 := by dsimp only [δ]; exact Real.sq_sqrt (by positivity)
  have hVcancel : FullEulerBound.eulerConstant^2*V=η/2 := by dsimp only [V]; field_simp [hC.ne']
  obtain ⟨N₁,hN₁,hcount⟩ := CommonUnitException.bad_units_card_small ζ hζ
  obtain ⟨N₂,hN₂⟩ := eventually_atTop.mp
    (SlowPrimeBandSieve.reciprocal_mass_tendsto.eventually
      (eventually_ge_atTop (8*(FullEulerBound.harmonicConstant+1-Real.log δ))))
  refine ⟨max (max N₁ N₂) 2,le_max_right _ _,?_⟩
  intro N hN M T hT1 hMT hNT
  let K : ℕ := ⌈T+(M : ℝ)⌉₊
  have hcover : T+(M : ℝ) ≤ (K : ℝ) := Nat.le_ceil _
  have hceil : (K : ℝ) < T+(M : ℝ)+1 := Nat.ceil_lt_add_one (by positivity)
  have hK7 : 2*(K : ℝ)+1 ≤ 7*T := by linarith
  have hNK : (SlowPrimeBandSieve.upper N)^3 ≤ (K : ℝ) := hNT.trans (by have hh := Nat.cast_nonneg (α := ℝ) M; linarith)
  have hcard := hcount N (by omega) K hNK
  have hmass := hN₂ N (by omega)
  let E := ShiftedExceptionWeight.largeShifts N K M T V
  refine ⟨E,ShiftedExceptionWeight.largeShifts_measurable N K M T V,?_,?_,?_⟩
  · intro τ hτ
    exact hτ.1
  · have hexc := FullEulerEnvelope.exceptional_measure N K
    have hsize := mul_le_mul_of_nonneg_left hK7 hζ.le
    have hmeas : volume.real (FullEulerEnvelope.exceptional N K) ≤ 14*ζ*T := by nlinarith
    have hmark := ShiftedExceptionWeight.largeShifts_budget N K M T (by linarith) V
    have hbound : V*volume.real E ≤ 70*ζ*T := hmark.trans (by nlinarith)
    have heq : 70*ζ*T=V*(ε*T) := by dsimp only [ζ]; ring
    rw [heq] at hbound
    exact _root_.le_of_mul_le_mul_left hbound hV
  · intro X hNX f hf τ hτ hnot
    have hbad := ShiftedExceptionWeight.off_largeShifts N K M T V τ hτ hnot
    have henv := FullEulerEnvelope.shifted_budget_envelope N X (by omega) (by omega) hNX δ hδ hmass
      K M T hcover τ ⟨hτ.1.le,hτ.2⟩ f hf
    have hsmall : 5*δ^2+FullEulerBound.eulerConstant^2*FullEulerEnvelope.badWeight N K M τ ≤ η := by
      calc
        _ ≤ 5*δ^2+FullEulerBound.eulerConstant^2*V :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hbad.le (sq_nonneg _))
        _ = _ := by rw [hδsq,hVcancel]; ring
    exact henv.trans (by
      have hh := mul_le_mul_of_nonneg_left hsmall (sq_nonneg (Real.log (X : ℝ)))
      simpa only [mul_comm] using hh)
end PaperP1.CommonFullEulerBudget
