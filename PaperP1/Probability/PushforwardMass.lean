module

public import PaperP1.Probability.AtomicTests
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Actual probability laws from countable real mass pushforwards -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PushforwardMass

open MeasureTheory PaperP1.AtomicProbability PaperP1.AtomicTests

variable {ι : Type*}

def map (φ : ι → ℕ) (a : ι → ℝ) (k : ℕ) : ℝ := ∑' i : {i // φ i = k}, a i.val

theorem hasSum_map {a : ι → ℝ} {s : ℝ} (ha : HasSum a s) (φ : ι → ℕ) : HasSum (map φ a) s :=
  ha.tsum_fiberwise φ

theorem map_nonneg {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (φ : ι → ℕ) (k : ℕ) : 0 ≤ map φ a k :=
  tsum_nonneg (fun i ↦ ha i.val)

theorem map_mul (φ : ι → ℕ) (a : ι → ℝ) (f : ℕ → ℝ) (k : ℕ) :
    map φ (fun i ↦ a i * f (φ i)) k = map φ a k * f k := by
  unfold map
  rw [← tsum_mul_right]
  apply tsum_congr
  intro i
  change a i.val * f (φ i.val) = a i.val * f k
  rw [i.property]

theorem summable_test_map (φ : ι → ℕ) (a : ι → ℝ) (f : ℕ → ℝ)
    (ha : Summable (fun i ↦ a i * f (φ i))) : Summable (fun k ↦ map φ a k * f k) := by
  have heq : map φ (fun i ↦ a i * f (φ i)) = (fun k ↦ map φ a k * f k) := funext (map_mul φ a f)
  simpa only [heq] using (hasSum_map ha.hasSum φ).summable

theorem test_map (φ : ι → ℕ) (a : ι → ℝ) (f : ℕ → ℝ)
    (ha : Summable (fun i ↦ a i * f (φ i))) :
    (∑' k, map φ a k * f k) = ∑' i, a i * f (φ i) := by
  have heq : map φ (fun i ↦ a i * f (φ i)) = (fun k ↦ map φ a k * f k) := funext (map_mul φ a f)
  simpa only [heq] using (hasSum_map ha.hasSum φ).tsum_eq

def law (φ : ι → ℕ) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hnorm : HasSum a 1) : ProbabilityMeasure ℕ :=
  ofMass (map φ a) (map_nonneg ha φ) (hasSum_map hnorm φ)

theorem realMass_law (φ : ι → ℕ) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hnorm : HasSum a 1) (k : ℕ) :
    realMass (law φ a ha hnorm) k = map φ a k :=
  ofMass_real_singleton _ _ _ _

theorem expectation_law (φ : ι → ℕ) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hnorm : HasSum a 1)
    (f : ℕ → ℝ) (hs : Summable (fun i ↦ a i * f (φ i))) :
    expectation (law φ a ha hnorm) f = ∑' i, a i * f (φ i) := by
  unfold expectation
  simp only [realMass_law]
  exact test_map φ a f hs

theorem realMass_map [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι]
    (P : ProbabilityMeasure ι) (φ : ι → ℕ) (hφ : Measurable φ) (k : ℕ) :
    realMass (P.map φ) k = map φ (fun i ↦ (P : Measure ι).real {i}) k := by
  change ((P : Measure ι).map φ).real {k} = _
  rw [map_measureReal_apply hφ (measurableSet_singleton k)]
  have hi : IntegrableOn (fun _ : ι ↦ (1 : ℝ)) (φ ⁻¹' {k}) (P : Measure ι) :=
    integrableOn_const (measure_ne_top _ _)
  have h := setIntegral_countable (fun _ : ι ↦ (1 : ℝ)) (Set.to_countable (φ ⁻¹' {k})) hi
  have heq : φ ⁻¹' ({k} : Set ℕ) = {i | φ i = k} := by ext i; simp
  rw [heq] at h
  rw [heq]
  convert h using 1
  · simp only [setIntegral_const, smul_eq_mul, mul_one]
  · simp only [smul_eq_mul, mul_one]
    let e : {i // φ i = k} ≃ ({i | φ i = k} : Set ι) :=
      { toFun := fun i ↦ ⟨i.val, by simpa only [Set.mem_ofPred_eq] using i.property⟩
        invFun := fun i ↦ ⟨i.val, by simpa only [Set.mem_ofPred_eq] using i.property⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    unfold map
    exact e.tsum_eq (fun i ↦ (P : Measure ι).real {i.val})

end PaperP1.PushforwardMass
