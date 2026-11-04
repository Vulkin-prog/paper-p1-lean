module

public import PaperP1.Model.PairPrimitiveCompression
public import PaperP1.Model.OneTargetCrossing

/-! # A positive crossing above a dependent pair produces a connected triple -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DependentPairCrossingConnected

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem singleton_primitive (L : ℕ) (e : Finset ℕ) (z : ℕ) (hz : z ∉ e)
    (hcross : 0 < OneTargetCrossing.rank e L z) : PairPrimitiveCompression.Primitive L e {z} := by
  classical
  let : Fintype (FixedPairExtensions.sourceSpace e L) :=
    MinimalRelativeRelations.spanFintype (fun x ↦ squareClassSpace x L) e
  have hdis : Disjoint e ({z} : Finset ℕ) := disjoint_singleton_right.mpr hz
  have hu := MinimalRelativeRelations.source_union_identity (fun x ↦ squareClassSpace x L) e {z} hdis
  have hi := OneTargetCrossing.nullity_insert e L z hz
  rw [union_singleton] at hu
  change runRelativeNullity L (insert z e) = runRelativeNullity L e +
    PairPrimitiveCompression.nullity L e {z} at hu
  refine ⟨hdis, RetainedNullity.nullity_singleton _ z, by omega, ?_⟩
  intro B hB
  rw [eq_empty_of_ssubset_singleton hB]
  exact MinimalRelativeRelations.nullity_empty _ _

theorem connected (L : ℕ) (e : Finset ℕ) (z : ℕ) (he : e.card = 2)
    (hdep : 0 < runRelativeNullity L e) (hz : z ∉ e)
    (hcross : 0 < OneTargetCrossing.rank e L z) :
    ConnectedWindowFamilies.Connected L (e ∪ {z}) :=
  PairPrimitiveCompression.connected L e {z} he hdep (singleton_primitive L e z hz hcross)

end PaperP1.DependentPairCrossingConnected
