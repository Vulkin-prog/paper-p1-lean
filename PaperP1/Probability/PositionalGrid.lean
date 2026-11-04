module

public import PaperP1.Probability.PositionalGroundSupport
public import PaperP1.Probability.PositionalCountProjection
public import PaperP1.Probability.PositionalProbabilityMeasure

/-! # Exact identification with configurations on the original finite grid -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalGrid

open Finset MeasureTheory PaperP1.PositionalFiniteLaw PaperP1.PositionalGroundSupport
  PaperP1.CompletedPositionalLaw PaperP1.PositionalTotalMass PaperP1.PositivePositionalConvolution

variable {ι Ω : Type*}

def encode (G : Finset ι) (z : G → ℕ) : Configuration ι :=
  ∑ x : G, Finsupp.single x.val (z x)

@[simp] theorem encode_apply_mem (G : Finset ι) (z : G → ℕ) (x : G) :
    encode G z x.val = z x := by
  classical
  simp [encode, Finset.sum_apply', Finsupp.single_apply]

theorem encode_apply_outside (G : Finset ι) (z : G → ℕ) (x : ι) (hx : x ∉ G) :
    encode G z x = 0 := by
  classical
  unfold encode
  rw [Finset.sum_apply']
  apply sum_eq_zero
  intro y _
  have hne : y.val ≠ x := by intro he; exact hx (he ▸ y.property)
  simp [hne]

theorem encode_onGround (G : Finset ι) (z : G → ℕ) : OnGround G (encode G z) :=
  fun x hx ↦ encode_apply_outside G z x hx

theorem encode_injective (G : Finset ι) : Function.Injective (encode G) := by
  intro z w hzw
  funext x
  have hh := congrArg (fun v : Configuration ι ↦ v x.val) hzw
  simpa only [encode_apply_mem] using hh

theorem encode_restrict (G : Finset ι) (v : Configuration ι) (hv : OnGround G v) :
    encode G (fun x ↦ v x.val) = v := by
  classical
  ext x
  by_cases hx : x ∈ G
  · exact encode_apply_mem G _ ⟨x, hx⟩
  · rw [encode_apply_outside G _ x hx, hv x hx]

theorem totalCount_encode (G : Finset ι) (z : G → ℕ) :
    PositionalCountProjection.totalCount (encode G z) = ∑ x : G, z x := by
  simp [encode]

theorem configuration_apply_mem (G : Finset ι) (J : ι → Ω → Bool) (ω : Ω) (x : G) :
    configuration G J ω x.val = (J x.val ω).toNat := by
  classical
  simp [configuration, Finset.sum_apply', Finsupp.single_apply, x.property]

theorem configuration_eq_encode (G : Finset ι) (J : ι → Ω → Bool) (ω : Ω) (z : G → ℕ) :
    configuration G J ω = encode G z ↔ ∀ x : G, (J x.val ω).toNat = z x := by
  constructor
  · intro hh x
    have he := congrArg (fun v : Configuration ι ↦ v x.val) hh
    simpa only [configuration_apply_mem, encode_apply_mem] using he
  · intro hh
    have he := encode_restrict G (configuration G J ω) (onGround_configuration G J ω)
    rw [← he]
    apply congrArg (encode G)
    funext x
    rw [configuration_apply_mem, hh x]

theorem tsum_grid_eq (G : Finset ι) (f : Configuration ι → ℝ)
    (hf : ∀ v, ¬ OnGround G v → f v = 0) :
    (∑' z : G → ℕ, f (encode G z)) = ∑' v, f v := by
  apply (encode_injective G).tsum_eq
  intro v hv
  have hground : OnGround G v := by
    by_contra hn
    exact hv (hf v hn)
  exact ⟨fun x ↦ v x.val, encode_restrict G v hground⟩

theorem hasSum_grid_coeff (G : Finset ι) (ν : Space ι)
    (hν : IsProbability ν) (hG : Supported G ν) :
    HasSum (fun z : G → ℕ ↦ coeff (encode G z) ν) 1 := by
  have hs := (summable_coeff ν).comp_injective (encode_injective G)
  have hh := hs.hasSum
  change HasSum (fun z : G → ℕ ↦ coeff (encode G z) ν)
    (∑' z : G → ℕ, coeff (encode G z) ν) at hh
  rw [tsum_grid_eq G _ hG, ← totalMass_eq_tsum, hν.2] at hh
  exact hh

def law (G : Finset ι) (ν : Space ι) (hν : IsProbability ν) (hG : Supported G ν) :
    ProbabilityMeasure (G → ℕ) :=
  ⟨Measure.sum (fun z : G → ℕ ↦ ENNReal.ofReal (coeff (encode G z) ν) • Measure.dirac z),
    (hasSum_grid_coeff G ν hν hG).isProbabilityMeasure_sum_dirac (fun _z ↦ hν.1 _)⟩

theorem real_singleton (G : Finset ι) (ν : Space ι) (hν : IsProbability ν)
    (hG : Supported G ν) (z : G → ℕ) :
    (law G ν hν hG : Measure (G → ℕ)).real {z} = coeff (encode G z) ν := by
  change ((Measure.sum (fun w : G → ℕ ↦
    ENNReal.ofReal (coeff (encode G w) ν) • Measure.dirac w)) {z}).toReal = _
  rw [Measure.sum_smul_dirac_singleton, ENNReal.toReal_ofReal (hν.1 _)]

theorem weighted_difference_eq (G : Finset ι) (ν κ : Space ι)
    (hν : Supported G ν) (hκ : Supported G κ) (j : ℕ) :
    (∑' z : G → ℕ, (1 + ∑ x : G, (z x : ℝ)) ^ j *
      |coeff (encode G z) ν - coeff (encode G z) κ|) =
      ∑' v : Configuration ι, (1 + (PositionalCountProjection.totalCount v : ℝ)) ^ j *
        |coeff v ν - coeff v κ| := by
  calc
    _ = ∑' z : G → ℕ,
        (1 + (PositionalCountProjection.totalCount (encode G z) : ℝ)) ^ j *
          |coeff (encode G z) ν - coeff (encode G z) κ| := by
      simp only [totalCount_encode, Nat.cast_sum]
    _ = _ := tsum_grid_eq G
      (fun v ↦ (1 + (PositionalCountProjection.totalCount v : ℝ)) ^ j * |coeff v ν - coeff v κ|)
      (fun v hv ↦ by
      rw [hν v hv, hκ v hv, sub_self, abs_zero, mul_zero])

end PaperP1.PositionalGrid
