module

public import PaperP1.Algebra.QuadraticTowerSigns
public import PaperP1.Algebra.IndependentQuadraticTower
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.Adjoin.PowerBasis
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # The actual radical sum generates every independent multiquadratic tower -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimitiveRadicalSum

open Finset Module PaperP1.FiniteQuadraticTower PaperP1.FiniteRadicalProjection
  PaperP1.QuadraticTowerSigns

theorem signedSum_minpoly (K : Type*) [Field K] [CharZero K] (s : List K)
    (ε : Fin s.length → Bool) :
    Polynomial.aeval (signedSum K s ε) (minpoly K (radicalSum K s)) = 0 := by
  rw [← map_radicalSum]
  exact minpoly.aeval_algHom K (signHom K s ε) (radicalSum K s)

theorem degree_lower (K : Type*) [Field K] [CharZero K] (s : List K) [IsDomain (Tower K s)] :
    2 ^ s.length ≤ (minpoly K (radicalSum K s)).natDegree := by
  classical
  let p := (minpoly K (radicalSum K s)).map (algebraMap K (Tower K s))
  have hroots : (sumOrbit K s).val ⊆ p.roots := by
    intro z hz
    have hz' : z ∈ sumOrbit K s := hz
    obtain ⟨ε, _hε, rfl⟩ := mem_image.mp hz'
    apply (Polynomial.mem_roots_map_of_injective (base_injective K s) (minpoly.ne_zero (sum_integral K s))).mpr
    exact signedSum_minpoly K s ε
  have hh := Polynomial.card_le_degree_of_subset_roots hroots
  rw [sumOrbit_card] at hh
  simpa only [p, Polynomial.natDegree_map] using hh

theorem minpoly_degree (K : Type*) [Field K] [CharZero K] (s : List K) [IsDomain (Tower K s)] :
    (minpoly K (radicalSum K s)).natDegree = 2 ^ s.length := by
  have hdeg : finrank K (imageAlgebra K s) = (minpoly K (radicalSum K s)).natDegree :=
    (Algebra.adjoin.powerBasis (sum_integral K s)).finrank
  have hle : (minpoly K (radicalSum K s)).natDegree ≤ finrank K (Tower K s) := by
    rw [← hdeg]
    exact (imageAlgebra K s).toSubmodule.finrank_le
  rw [FiniteQuadraticTower.finrank] at hle
  exact le_antisymm hle (degree_lower K s)

theorem adjoin_sum_eq_top (K : Type*) [Field K] [CharZero K] (s : List K) [IsDomain (Tower K s)] :
    imageAlgebra K s = ⊤ := by
  apply Subalgebra.toSubmodule_injective
  apply Submodule.eq_top_of_finrank_eq
  calc
    finrank K (imageAlgebra K s) = (minpoly K (radicalSum K s)).natDegree :=
      (Algebra.adjoin.powerBasis (sum_integral K s)).finrank
    _ = finrank K (Tower K s) := (minpoly_degree K s).trans (FiniteQuadraticTower.finrank K s).symm

theorem independent_sum_primitive (K : Type*) [Field K] [CharZero K] (s : List K)
    (hs : IndependentQuadraticTower.Independent s) :
    imageAlgebra K s = ⊤ ∧ (minpoly K (radicalSum K s)).natDegree = 2 ^ s.length := by
  let : Field (Tower K s) := (IndependentQuadraticTower.isField K s hs).toField
  exact ⟨adjoin_sum_eq_top K s, minpoly_degree K s⟩

end PaperP1.PrimitiveRadicalSum
