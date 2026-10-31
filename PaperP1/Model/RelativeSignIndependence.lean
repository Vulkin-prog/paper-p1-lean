module

public import PaperP1.Affine.IndependentRows
public import PaperP1.Model.LocalRunRank
public import PaperP1.Coding.LocalRigidityRegimes
public import Mathlib.Probability.Independence.Basic

/-!
# Exact independence of actual relative signs

With no even square relation in a window, the full vector of relative bits
has the fair product law under the infinite prime-sign measure. Independence
is stated with Mathlib's `iIndepFun`, then transported to the actual signs.
The last theorem supplies one threshold for every subcritical window.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RelativeSignIndependence

open MeasureTheory ProbabilityTheory PaperP1.Arithmetic PaperP1.Affine PaperP1.Algebra
open PaperP1.Model PaperP1.Model.InfiniteRademacher
open PaperP1.Probability PaperP1.Probability.CylinderExpectations
open PaperP1.Probability.InfiniteCylinderTransfer
open WindowRelationCode

local instance relativeSignsPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance relativeSignsMeasurableF2 : MeasurableSpace F₂ := ⊤

def infiniteStartBits (x L : ℕ) (ω : InfiniteSample) (i : Fin L) : F₂ :=
  if i.val = 0 then infiniteValueBit ω (x - 1) + infiniteValueBit ω x
  else infiniteValueBit ω x + infiniteValueBit ω (x + i.val)

theorem startSystem_restrict_eq {M x L : ℕ} (hcut : x + L ≤ M) (ω : InfiniteSample) :
    startSystem M x L (restrictToFinite M ω) = infiniteStartBits x L ω := by
  funext i
  rw [startSystem_apply, infiniteStartBits]
  by_cases hi : i.val = 0
  · simp only [hi, ite_true]
    rw [valueBit_restrictToFinite_eq_infiniteValueBit ω (by omega),
      valueBit_restrictToFinite_eq_infiniteValueBit ω (by omega)]
  · simp only [hi, ite_false]
    rw [valueBit_restrictToFinite_eq_infiniteValueBit ω (by omega),
      valueBit_restrictToFinite_eq_infiniteValueBit ω (by have := i.isLt; omega)]

theorem measurable_infiniteStartBits (x L : ℕ) : Measurable (infiniteStartBits x L) := by
  have heq : infiniteStartBits x L =
      (startSystem (x + L) x L) ∘ restrictToFinite (x + L) := by
    funext ω
    exact (startSystem_restrict_eq le_rfl ω).symm
  rw [heq]
  exact Measurable.of_discrete.comp (measurable_restrictToFinite (x + L))

theorem infiniteStartBits_atom_eq_finite {M x L : ℕ} (hcut : x + L ≤ M) (b : Fin L → F₂) :
    infiniteRademacherMeasure.real {ω | infiniteStartBits x L ω = b} =
      uniformSolutionMass (startSystem M x L) b := by
  classical
  have hs : MeasurableSet {ω | infiniteStartBits x L ω = b} :=
    (measurable_infiniteStartBits x L) (measurableSet_singleton b)
  rw [← integral_indicator_one hs]
  simp only [Set.indicator_apply, Pi.one_apply, Set.mem_ofPred_eq]
  have heq : (fun ω ↦ if infiniteStartBits x L ω = b then (1 : ℝ) else 0) =
      (fun ω ↦ if startSystem M x L (restrictToFinite M ω) = b then 1 else 0) := by
    funext ω
    rw [startSystem_restrict_eq hcut]
  rw [heq]
  calc
    _ = finiteExpectation (cylinderProbability M).weight
        (fun σ : SampleSpace M ↦ if startSystem M x L σ = b then (1 : ℝ) else 0) :=
      infiniteCylinder_integral M _
    _ = uniformSolutionMass (startSystem M x L) b := by
      unfold uniformSolutionMass
      congr 1
      funext σ
      by_cases h : startSystem M x L σ = b <;> simp [h]

theorem full_effective_rank_of_no_relation {M x L : ℕ} (hx : 0 < x) (hcut : x + L ≤ M)
    (hrel : Module.finrank F₂ (windowRelationCode (x - 1) (L + 1)) = 0) :
    Module.finrank F₂ (effectiveRowSpace (startSystem M x L)) = L := by
  have h := LocalRunRank.squareClass_rank_add_relation_rank (L := L) hx
  rw [hrel, add_zero] at h
  exact (finrank_squareClassSpace_eq_effectiveRows hcut).symm.trans h

theorem infiniteStartBits_atom_uniform {x L : ℕ} (hx : 0 < x)
    (hrel : Module.finrank F₂ (windowRelationCode (x - 1) (L + 1)) = 0)
    (b : Fin L → F₂) :
    infiniteRademacherMeasure.real {ω | infiniteStartBits x L ω = b} = (2 ^ L : ℝ)⁻¹ := by
  rw [infiniteStartBits_atom_eq_finite (M := x + L) le_rfl]
  have hr := full_effective_rank_of_no_relation hx (M := x + L) le_rfl hrel
  have hr' : Module.finrank F₂ (effectiveRowSpace (startSystem (x + L) x L)) =
      Fintype.card (Fin L) := by simpa only [Fintype.card_fin] using hr
  simpa only [Fintype.card_fin] using
    uniformSolutionMass_of_full_effective_rank (startSystem (x + L) x L) hr' b

theorem map_infiniteStartBits_eq_pi {x L : ℕ} (hx : 0 < x)
    (hrel : Module.finrank F₂ (windowRelationCode (x - 1) (L + 1)) = 0) :
    infiniteRademacherMeasure.map (infiniteStartBits x L) =
      Measure.pi (fun _ : Fin L ↦ coordinateMeasure) := by
  classical
  apply Measure.ext_of_singleton
  intro b
  apply (measureReal_eq_measureReal_iff).mp
  rw [map_measureReal_apply (measurable_infiniteStartBits x L) (measurableSet_singleton b)]
  change infiniteRademacherMeasure.real {ω | infiniteStartBits x L ω = b} = _
  rw [infiniteStartBits_atom_uniform hx hrel b]
  rw [Measure.real, Measure.pi_singleton]
  simp [coordinateMeasure, Measure.uniformOfFinset_apply_singleton, ZMod.card]

theorem iIndepFun_infiniteStartBits {x L : ℕ} (hx : 0 < x)
    (hrel : Module.finrank F₂ (windowRelationCode (x - 1) (L + 1)) = 0) :
    iIndepFun (fun i ω ↦ infiniteStartBits x L ω i) infiniteRademacherMeasure := by
  have hm := measurable_infiniteStartBits x L
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (fun i ↦ ((measurable_pi_apply i).comp hm).aemeasurable)).mpr
  change infiniteRademacherMeasure.map (infiniteStartBits x L) =
    Measure.pi (fun i : Fin L ↦ infiniteRademacherMeasure.map
      (fun ω ↦ infiniteStartBits x L ω i))
  rw [map_infiniteStartBits_eq_pi hx hrel]
  congr 1
  funext i
  calc
    coordinateMeasure = (Measure.pi (fun _ : Fin L ↦ coordinateMeasure)).map
        (Function.eval i) := (measurePreserving_eval (μ := fun _ : Fin L ↦ coordinateMeasure) i).map_eq.symm
    _ = (infiniteRademacherMeasure.map (infiniteStartBits x L)).map (Function.eval i) := by
      rw [map_infiniteStartBits_eq_pi hx hrel]
    _ = infiniteRademacherMeasure.map (fun ω ↦ infiniteStartBits x L ω i) :=
      Measure.map_map (measurable_pi_apply i) hm

/-- The vertices other than x, in the window {x-1,...,x+L-1}. -/
def relativeVertex (x L : ℕ) (i : Fin L) : ℕ := if i.val = 0 then x - 1 else x + i.val

def relativeSign (x L : ℕ) (i : Fin L) (ω : InfiniteSample) : ℤ :=
  infiniteRandomValue ω (relativeVertex x L i) * infiniteRandomValue ω x

theorem relativeSign_eq_phase_bits (x L : ℕ) (i : Fin L) (ω : InfiniteSample) :
    relativeSign x L i ω = phase (infiniteStartBits x L ω i) := by
  by_cases hi : i.val = 0
  · simp [relativeSign, relativeVertex, infiniteRandomValue, infiniteStartBits, hi, phase_add]
  · simp [relativeSign, relativeVertex, infiniteRandomValue, infiniteStartBits, hi, phase_add, mul_comm]

theorem iIndepFun_relativeSigns {x L : ℕ} (hx : 0 < x)
    (hrel : Module.finrank F₂ (windowRelationCode (x - 1) (L + 1)) = 0) :
    iIndepFun (relativeSign x L) infiniteRademacherMeasure := by
  have h := (iIndepFun_infiniteStartBits hx hrel).comp
    (fun _ ↦ phase) (fun _ ↦ Measurable.of_discrete)
  simpa only [Function.comp_def, ← relativeSign_eq_phase_bits] using h

/-- Exact independence under the actual infinite measure for every shorter
subcritical window, with a threshold before all bases and lengths. -/
theorem subcritical_relative_signs_independent (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ U L : ℕ,
      a * N ≤ (U : ℝ) → ((L + 1 : ℕ) : ℝ) ≤ (1 - ε) * Real.log N →
        iIndepFun (relativeSign (U + 1) L) infiniteRademacherMeasure := by
  obtain ⟨N₀, hN₀⟩ := UniformLocalRigidity.uniform_subcritical_relation_rank_zero a ε ha hε
  refine ⟨N₀, fun N hN U L hbase hwidth ↦ ?_⟩
  apply iIndepFun_relativeSigns (by omega : 0 < U + 1)
  have harg : U + 1 - 1 = U := by omega
  exact (congrArg (fun v : ℕ ↦ Module.finrank F₂ (windowRelationCode v (L + 1))) harg).trans
    (hN₀ N hN U (L + 1) hbase hwidth)

/-- Literal positive vertex count B, with relative-sign family indexed by B-1. -/
theorem subcritical_window_relative_signs_independent (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ U B : ℕ,
      1 ≤ B → a * N ≤ (U : ℝ) → (B : ℝ) ≤ (1 - ε) * Real.log N →
        iIndepFun (relativeSign (U + 1) (B - 1)) infiniteRademacherMeasure := by
  obtain ⟨N₀, hN₀⟩ := subcritical_relative_signs_independent a ε ha hε
  refine ⟨N₀, fun N hN U B hB hbase hwidth ↦ ?_⟩
  apply hN₀ N hN U (B - 1) hbase
  simpa only [Nat.sub_add_cancel hB] using hwidth

end PaperP1.RelativeSignIndependence
