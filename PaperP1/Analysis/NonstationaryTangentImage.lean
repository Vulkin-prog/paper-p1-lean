module

public import PaperP1.Analysis.PolynomialTangentTrajectory
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.Separation.Connected

/-! # Actual nonstationary trajectory images and their defining equation

A nonzero velocity gives infinitely many distinct image points on an interval.
The defining polynomial is constant along every tangent trajectory.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NonstationaryTangentImage

open Set MvPolynomial PolynomialTangentTrajectory PolynomialTangentDegree

def position (φ : Fin 2 → ℝ → ℝ) (t : ℝ) : Fin 2 → ℝ := fun i ↦ φ i t

theorem continuousOn_position (P : MvPolynomial (Fin 2) ℝ) (φ : Fin 2 → ℝ → ℝ)
    (s : Set ℝ) (hφ : Trajectory P φ s) : ContinuousOn (position φ) s := by
  apply continuousOn_pi.mpr
  intro i
  exact HasDerivAt.continuousOn (fun t ht ↦ hφ t ht i)

theorem image_nontrivial (P : MvPolynomial (Fin 2) ℝ) (φ : Fin 2 → ℝ → ℝ)
    (a b : ℝ) (hφ : Trajectory P φ (Ioo a b))
    (hactive : ∃ t ∈ Ioo a b, ∃ i, velocity P (position φ t) i ≠ 0) :
    (position φ '' Ioo a b).Nontrivial := by
  by_contra hbad
  have hsmall := Set.not_nontrivial_iff.mp hbad
  obtain ⟨t, ht, i, hi⟩ := hactive
  have heq : EqOn (φ i) (fun _ ↦ φ i t) (Ioo a b) := by
    intro u hu
    exact congrFun (hsmall (Set.mem_image_of_mem (position φ) hu)
      (Set.mem_image_of_mem (position φ) ht)) i
  have hzero := heq.deriv isOpen_Ioo ht
  rw [deriv_const] at hzero
  exact hi ((hφ t ht i).deriv.symm.trans hzero)

theorem image_infinite (P : MvPolynomial (Fin 2) ℝ) (φ : Fin 2 → ℝ → ℝ)
    (a b : ℝ) (hφ : Trajectory P φ (Ioo a b))
    (hactive : ∃ t ∈ Ioo a b, ∃ i, velocity P (position φ t) i ≠ 0) :
    (position φ '' Ioo a b).Infinite :=
  (isPreconnected_Ioo.image (position φ) (continuousOn_position P φ (Ioo a b) hφ)).infinite_of_nontrivial
    (image_nontrivial P φ a b hφ hactive)

theorem image_infinite_subinterval (P : MvPolynomial (Fin 2) ℝ) (φ : Fin 2 → ℝ → ℝ)
    (s : Set ℝ) (hφ : Trajectory P φ s)
    (hnon : ∀ t ∈ s, ∃ i, velocity P (position φ t) i ≠ 0)
    (a b : ℝ) (hab : a < b) (hsub : Ioo a b ⊆ s) :
    (position φ '' Ioo a b).Infinite := by
  have hm : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  exact image_infinite P φ a b (fun t ht ↦ hφ t (hsub ht))
    ⟨(a + b) / 2, hm, hnon _ (hsub hm)⟩

theorem equation_constant (P : MvPolynomial (Fin 2) ℝ) (φ : Fin 2 → ℝ → ℝ)
    (a b : ℝ) (hφ : Trajectory P φ (Ioo a b))
    (t u : ℝ) (ht : t ∈ Ioo a b) (hu : u ∈ Ioo a b) :
    eval (position φ t) P = eval (position φ u) P := by
  have hd : DifferentiableOn ℝ (fun v ↦ eval (position φ v) P) (Ioo a b) :=
    fun v hv ↦ (hasDerivAt_evaluation P P φ (Ioo a b) hφ v hv).differentiableAt.differentiableWithinAt
  have hz : EqOn (deriv (fun v ↦ eval (position φ v) P)) 0 (Ioo a b) := by
    intro v hv
    change deriv (fun u ↦ eval (fun j ↦ φ j u) P) v = 0
    rw [deriv_evaluation P P φ (Ioo a b) hφ v hv, tangent_self, map_zero]
  exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hd hz ht hu

theorem equation_zero (P : MvPolynomial (Fin 2) ℝ) (φ : Fin 2 → ℝ → ℝ)
    (a b : ℝ) (hφ : Trajectory P φ (Ioo a b)) (t : ℝ) (ht : t ∈ Ioo a b)
    (hzero : eval (position φ t) P = 0) : ∀ u ∈ Ioo a b, eval (position φ u) P = 0 := by
  intro u hu
  exact (equation_constant P φ a b hφ u t hu ht).trans hzero

end PaperP1.NonstationaryTangentImage
