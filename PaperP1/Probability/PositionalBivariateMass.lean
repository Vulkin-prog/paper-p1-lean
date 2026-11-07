module

public import PaperP1.Probability.PositionalBivariateLaw

/-! # Finite point probabilities for the bivariate reference law -/

set_option autoImplicit false
@[expose] public noncomputable section

namespace PaperP1.PositionalBivariateMass

open Finset MeasureTheory ProbabilityTheory
open scoped NNReal

def fiber (m n : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (Finset.range (min m n+1)).image fun k ↦ (m-k,(n-k,k))

theorem fiber_coe (m n : ℕ) :
    (↑(fiber m n) : Set (ℕ × (ℕ × ℕ)))=
      PositionalBivariateLaw.addCommon ⁻¹' {(m,n)} := by
  classical
  ext z
  rcases z with ⟨u,v,w⟩
  change (u,(v,w))∈fiber m n ↔ PositionalBivariateLaw.addCommon (u,(v,w))=(m,n)
  constructor
  · intro hz
    obtain ⟨k,hk,hz⟩ := Finset.mem_image.mp hz
    have hle : k≤min m n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hkm : k≤m := hle.trans (min_le_left m n)
    have hkn : k≤n := hle.trans (min_le_right m n)
    rw [← hz]
    simp only [PositionalBivariateLaw.addCommon,Nat.sub_add_cancel hkm,Nat.sub_add_cancel hkn]
  · intro hz
    have hm : u+w=m := congrArg Prod.fst hz
    have hn : v+w=n := congrArg Prod.snd hz
    have hw : w<min m n+1 := by omega
    apply Finset.mem_image.mpr
    refine ⟨w,Finset.mem_range.mpr hw,?_⟩
    apply Prod.ext
    · change m-w=u
      omega
    · apply Prod.ext
      · change n-w=v
        omega
      · rfl

theorem fiber_image_injective (m n : ℕ) :
    Function.Injective (fun k : ℕ ↦ (m-k,(n-k,k))) := by
  intro i j h
  exact congrArg (fun z : ℕ × (ℕ × ℕ) ↦ z.2.2) h

theorem real_singleton_product (a b c : ℝ≥0) (m n : ℕ) :
    (PositionalBivariateLaw.law a b c).real {(m,n)} =
      ∑ k∈Finset.range (min m n+1),
        (poissonMeasure a).real {m-k} * (poissonMeasure b).real {n-k} * (poissonMeasure c).real {k} := by
  classical
  rw [measureReal_def,PositionalBivariateLaw.law,
    Measure.map_apply PositionalBivariateLaw.measurable_addCommon (measurableSet_singleton (m,n))]
  change ((poissonMeasure a).prod ((poissonMeasure b).prod (poissonMeasure c))).real
    (PositionalBivariateLaw.addCommon ⁻¹' {(m,n)}) = _
  rw [← fiber_coe m n,
    ← sum_measureReal_singleton (μ := (poissonMeasure a).prod ((poissonMeasure b).prod (poissonMeasure c))) (fiber m n)]
  rw [fiber,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro k _hk
    rw [← Set.singleton_prod_singleton,measureReal_prod_prod,
      ← Set.singleton_prod_singleton,measureReal_prod_prod]
    exact mul_assoc _ _ _ |>.symm
  · exact fun _ _ _ _ h ↦ fiber_image_injective m n h

theorem exp_three (a b c : ℝ) :
    Real.exp (-a)*Real.exp (-b)*Real.exp (-c)=Real.exp (-(a+b+c)) := by
  rw [← Real.exp_add,← Real.exp_add]
  congr 1
  ring

theorem real_singleton (a b c : ℝ≥0) (m n : ℕ) :
    (PositionalBivariateLaw.law a b c).real {(m,n)} =
      Real.exp (-((a : ℝ)+(b : ℝ)+(c : ℝ))) *
        ∑ k∈Finset.range (min m n+1),
          (a : ℝ)^(m-k)*(b : ℝ)^(n-k)*(c : ℝ)^k /
            ((Nat.factorial (m-k) : ℝ)*(Nat.factorial (n-k) : ℝ)*(Nat.factorial k : ℝ)) := by
  rw [real_singleton_product,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [poissonMeasure_real_singleton,poissonMeasure_real_singleton,poissonMeasure_real_singleton]
  calc
    _ = (Real.exp (-(a : ℝ))*Real.exp (-(b : ℝ))*Real.exp (-(c : ℝ))) *
        ((a : ℝ)^(m-k)*(b : ℝ)^(n-k)*(c : ℝ)^k /
          ((Nat.factorial (m-k) : ℝ)*(Nat.factorial (n-k) : ℝ)*(Nat.factorial k : ℝ))) := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    _ = _ := by rw [exp_three]

theorem real_zero_zero (a b c : ℝ≥0) :
    (PositionalBivariateLaw.law a b c).real {(0,0)}=
      Real.exp (-((a : ℝ)+(b : ℝ)+(c : ℝ))) := by
  simpa using real_singleton a b c 0 0

theorem probability_of_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U V : Ω → ℕ) (a b c : ℝ≥0)
    (hLaw : HasLaw (fun ω ↦ (U ω,V ω)) (PositionalBivariateLaw.law a b c) P) (m n : ℕ) :
    P.real {ω | U ω=m ∧ V ω=n}=
      Real.exp (-((a : ℝ)+(b : ℝ)+(c : ℝ))) *
        ∑ k∈Finset.range (min m n+1),
          (a : ℝ)^(m-k)*(b : ℝ)^(n-k)*(c : ℝ)^k /
            ((Nat.factorial (m-k) : ℝ)*(Nat.factorial (n-k) : ℝ)*(Nat.factorial k : ℝ)) := by
  have h := hLaw.measureReal_eq (p := fun z ↦ z=(m,n)) (measurableSet_singleton (m,n))
  change P.real {ω | (U ω,V ω)=(m,n)}=(PositionalBivariateLaw.law a b c).real {(m,n)} at h
  simpa only [Prod.mk.injEq] using h.trans (real_singleton a b c m n)

theorem probability_pair_sums {α Ω : Type*} [DecidableEq α] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : α → ℝ≥0) (X : α → Ω → ℕ)
    (hX : ∀ i,HasLaw (X i) (poissonMeasure (μ i)) P) (hInd : iIndepFun X P)
    (S T : Finset α) (m n : ℕ) :
    let a : ℝ≥0 := ∑ i∈S\T,μ i
    let b : ℝ≥0 := ∑ i∈T\S,μ i
    let c : ℝ≥0 := ∑ i∈S∩T,μ i
    P.real {ω | (∑ i∈S,X i ω)=m ∧ (∑ i∈T,X i ω)=n}=
      Real.exp (-((a : ℝ)+(b : ℝ)+(c : ℝ))) *
        ∑ k∈Finset.range (min m n+1),
          (a : ℝ)^(m-k)*(b : ℝ)^(n-k)*(c : ℝ)^k /
            ((Nat.factorial (m-k) : ℝ)*(Nat.factorial (n-k) : ℝ)*(Nat.factorial k : ℝ)) := by
  exact probability_of_hasLaw P (fun ω ↦ ∑ i∈S,X i ω) (fun ω ↦ ∑ i∈T,X i ω)
    _ _ _ (PositionalBivariateLaw.hasLaw_pair_sums P μ X hX hInd S T) m n

end PaperP1.PositionalBivariateMass
