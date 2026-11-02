module

public import PaperP1.Probability.JumpPoissonSeries
public import PaperP1.Probability.QuadraticPoisson
public import Mathlib.Probability.Independence.Basic

/-! # Independent single and fixed-size Poisson jumps on an actual product space -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompoundPoissonSeries

open MeasureTheory PaperP1.Probability PaperP1.CompletedLaw PaperP1.CompletedPoisson
  PaperP1.JumpPoissonSeries PaperP1.PoissonSequence

def compound (j : ℕ) (a b : ℝ) : Space := poisson a * jumpPoisson j b

theorem atom_mul (u v : ℕ) : ofFinite (atom u) * ofFinite (atom v) = ofFinite (atom (u + v)) := by
  rw [← map_mul]
  congr 1
  simp only [atom, AddMonoidAlgebra.single_mul_single, one_mul]

theorem hasSum_compound (j : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    HasSum (fun z : ℕ × ℕ ↦ PoissonProduct.joint a b z • ofFinite (atom (z.1 + j * z.2)))
      (compound j a b) := by
  let f : ℕ → Space := fun n ↦ mass a n • ofFinite (atom n)
  let g : ℕ → Space := fun n ↦ mass b n • ofFinite (atom (j * n))
  have hf : HasSum f (poisson a) := by
    simpa only [f, one_mul, jump_one] using hasSum_jumpPoisson 1 a
  have hg : HasSum g (jumpPoisson j b) := hasSum_jumpPoisson j b
  have hfn : Summable (fun n ↦ ‖f n‖) := by simpa only [f, one_mul] using summable_norm 1 ha
  have hgn : Summable (fun n ↦ ‖g n‖) := summable_norm j hb
  have hfg : Summable (fun z : ℕ × ℕ ↦ f z.1 * g z.2) := summable_mul_of_summable_norm hfn hgn
  have h := hf.mul hg hfg
  convert h using 1
  · funext z
    simp only [f, g, smul_mul_smul_comm, atom_mul, PoissonProduct.joint]
  · rfl

theorem coeff_atom_series {ι : Type*} (φ : ι → ℕ) (w : ι → ℝ) (ν : Space)
    (hseries : HasSum (fun i ↦ w i • ofFinite (atom (φ i))) ν) (k : ℕ) :
    coeff k ν = PushforwardMass.map φ w k := by
  classical
  have h := hseries.map (coeff k) (coeff k).continuous
  dsimp only [Function.comp_def] at h
  have heq (i : ι) : coeff k (w i • ofFinite (atom (φ i))) = if φ i = k then w i else 0 := by
    simp only [map_smul, coeff_ofFinite, atom, AddMonoidAlgebra.coeff_single,
      Finsupp.single_apply, smul_eq_mul]
    split_ifs <;> simp
  simp_rw [heq] at h
  rw [← h.tsum_eq]
  unfold PushforwardMass.map
  change (∑' i : ι, if φ i = k then w i else 0) = ∑' i : ({i : ι | φ i = k} : Set ι), w i.val
  rw [tsum_subtype ({i : ι | φ i = k} : Set ι) w]
  exact tsum_congr (fun _ ↦ by simp only [Set.indicator_apply, Set.mem_ofPred_eq])

theorem coeff_compound (j : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (k : ℕ) :
    coeff k (compound j a b) =
      PushforwardMass.map (fun z : ℕ × ℕ ↦ z.1 + j * z.2) (PoissonProduct.joint a b) k :=
  coeff_atom_series _ _ _ (hasSum_compound j ha hb) k

def independentPoisson (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : ProbabilityMeasure (ℕ × ℕ) :=
  ⟨(QuadraticPoisson.poissonLaw a ha : Measure ℕ).prod (QuadraticPoisson.poissonLaw b hb : Measure ℕ), inferInstance⟩

theorem independent_coordinates (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ProbabilityTheory.IndepFun (Prod.fst : ℕ × ℕ → ℕ) Prod.snd (independentPoisson a b ha hb : Measure (ℕ × ℕ)) := by
  exact ProbabilityTheory.indepFun_prod measurable_id measurable_id

theorem first_coordinate_law (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (independentPoisson a b ha hb : Measure (ℕ × ℕ)).map Prod.fst = (QuadraticPoisson.poissonLaw a ha : Measure ℕ) := by
  change ((QuadraticPoisson.poissonLaw a ha : Measure ℕ).prod
    (QuadraticPoisson.poissonLaw b hb : Measure ℕ)).map Prod.fst = _
  rw [Measure.map_fst_prod, measure_univ, one_smul]

theorem second_coordinate_law (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (independentPoisson a b ha hb : Measure (ℕ × ℕ)).map Prod.snd = (QuadraticPoisson.poissonLaw b hb : Measure ℕ) := by
  change ((QuadraticPoisson.poissonLaw a ha : Measure ℕ).prod
    (QuadraticPoisson.poissonLaw b hb : Measure ℕ)).map Prod.snd = _
  rw [Measure.map_snd_prod, measure_univ, one_smul]

theorem independentPoisson_singleton (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (z : ℕ × ℕ) :
    (independentPoisson a b ha hb : Measure (ℕ × ℕ)).real {z} = PoissonProduct.joint a b z := by
  rcases z with ⟨m, n⟩
  change (((QuadraticPoisson.poissonLaw a ha : Measure ℕ).prod
    (QuadraticPoisson.poissonLaw b hb : Measure ℕ)) {(m, n)}).toReal = _
  rw [← Set.singleton_prod_singleton, Measure.prod_prod, ENNReal.toReal_mul]
  change (QuadraticPoisson.poissonLaw a ha : Measure ℕ).real {m} *
    (QuadraticPoisson.poissonLaw b hb : Measure ℕ).real {n} = mass a m * mass b n
  rw [show (QuadraticPoisson.poissonLaw a ha : Measure ℕ).real {m} = mass a m from
      ProbabilityTheory.poissonMeasure_real_singleton ⟨a, ha⟩ m,
    show (QuadraticPoisson.poissonLaw b hb : Measure ℕ).real {n} = mass b n from
      ProbabilityTheory.poissonMeasure_real_singleton ⟨b, hb⟩ n]

def law (j : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : ProbabilityMeasure ℕ :=
  (independentPoisson a b ha hb).map (fun z ↦ z.1 + j * z.2)

theorem realMass_law (j : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (k : ℕ) :
    AtomicProbability.realMass (law j a b ha hb) k =
      PushforwardMass.map (fun z : ℕ × ℕ ↦ z.1 + j * z.2) (PoissonProduct.joint a b) k := by
  simpa only [law, independentPoisson_singleton] using PushforwardMass.realMass_map
    (independentPoisson a b ha hb) (fun z : ℕ × ℕ ↦ z.1 + j * z.2) (measurable_of_countable _) k

theorem actual_signed_measure (j : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    toSignedMeasure (compound j a b) = (law j a b ha hb : Measure ℕ).toSignedMeasure := by
  apply AtomicSignedLaw.signedMeasure_ext_singleton
  intro k
  rw [toSignedMeasure_singleton, coeff_compound j ha hb,
    Measure.toSignedMeasure_apply_measurable (measurableSet_singleton k)]
  exact (realMass_law j a b ha hb k).symm

end PaperP1.CompoundPoissonSeries
