module

public import PaperP1.Arithmetic.PrivateEvenIntersection
public import PaperP1.Algebra.EvenReindex

/-! # Actual even selections of exact units parameterize the private pair intersection -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UnitIntersectionEquiv

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.NormalizedWindowSets PaperP1.NormalizedUnitCount

local instance unitIntersectionPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

def unitValue (a b x y L : ℕ) (u : ↥(units a b x y L)) : ↥(normalized b x L ∩ normalized a y L) :=
  ⟨b * startCompleteVertexLabel x L u.val.1, mem_inter.mpr
    ⟨mem_image.mpr ⟨_, mem_values.mpr ⟨u.val.1, rfl⟩, rfl⟩,
      mem_image.mpr ⟨_, mem_values.mpr ⟨u.val.2, rfl⟩, (mem_units.mp u.property).symm⟩⟩⟩

theorem unitValue_injective {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) (hy : 0 < y) :
    Function.Injective (unitValue a b x y L) := by
  intro u v heq
  have hval := congrArg (fun n : ↥(normalized b x L ∩ normalized a y L) ↦ n.val) heq
  change b * startCompleteVertexLabel x L u.val.1 = b * startCompleteVertexLabel x L v.val.1 at hval
  have hleft : u.val.1 = v.val.1 := startCompleteVertexLabel_injective hx (mul_left_cancel₀ hb.ne' hval)
  have hrightEq : a * startCompleteVertexLabel y L u.val.2 = a * startCompleteVertexLabel y L v.val.2 :=
    (mem_units.mp u.property).symm.trans (hval.trans (mem_units.mp v.property))
  have hright : u.val.2 = v.val.2 := startCompleteVertexLabel_injective hy (mul_left_cancel₀ ha.ne' hrightEq)
  exact Subtype.ext (Prod.ext hleft hright)

theorem unitValue_surjective (a b x y L : ℕ) : Function.Surjective (unitValue a b x y L) := by
  intro n
  obtain ⟨hnx, hny⟩ := mem_inter.mp n.property
  obtain ⟨nx, hxValues, hxEq⟩ := mem_image.mp hnx
  obtain ⟨ny, hyValues, hyEq⟩ := mem_image.mp hny
  obtain ⟨i, hi⟩ := mem_values.mp hxValues
  obtain ⟨j, hj⟩ := mem_values.mp hyValues
  have hunit : b * startCompleteVertexLabel x L i = a * startCompleteVertexLabel y L j := by
    rw [hi, hj]
    exact hxEq.trans hyEq.symm
  refine ⟨⟨(i, j), mem_units.mpr hunit⟩, Subtype.ext ?_⟩
  change b * startCompleteVertexLabel x L i = n.val
  rw [hi]
  exact hxEq

def valueEquiv {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) (hy : 0 < y) :
    ↥(units a b x y L) ≃ ↥(normalized b x L ∩ normalized a y L) :=
  Equiv.ofBijective (unitValue a b x y L) ⟨unitValue_injective ha hb hx hy, unitValue_surjective a b x y L⟩

theorem valueEquiv_apply_val {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) (hy : 0 < y)
    (u : ↥(units a b x y L)) :
    (valueEquiv ha hb hx hy u).val = b * startCompleteVertexLabel x L u.val.1 := rfl

def unitData (a b x y L : ℕ) : ↥(units a b x y L) → (ℕ →₀ F₂) :=
  fun u ↦ parityVec (b * startCompleteVertexLabel x L u.val.1)

def unitClassMap (a b x y L : ℕ) := EvenImage.evenMap (K := F₂) (unitData a b x y L)

def unitIntersectionEquiv {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hprivate : FiniteEvenSquareClasses.Private (NormalizedWindowSets.union a b x y L)) :
    LinearMap.ker (EvenSupportRank.sumMap F₂ ↥(units a b x y L)) ≃ₗ[F₂]
      ↥(squareClassSpace x L ⊓ squareClassSpace y L) :=
  (EvenReindex.reindex (K := F₂) (valueEquiv ha hb (by omega) (by omega))).trans
    ((PrivateEvenIntersection.intersectionEquiv hprivate).trans
      (LinearEquiv.ofEq _ _ (by rw [space_normalized hb hx, space_normalized ha hy])))

theorem unitIntersectionEquiv_apply {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hprivate : FiniteEvenSquareClasses.Private (NormalizedWindowSets.union a b x y L))
    (w : LinearMap.ker (EvenSupportRank.sumMap F₂ ↥(units a b x y L))) :
    (unitIntersectionEquiv ha hb hx hy hprivate w).val = unitClassMap a b x y L w := by
  change EvenImage.evenMap (FiniteEvenSquareClasses.data (normalized b x L ∩ normalized a y L))
      (EvenReindex.reindex (valueEquiv ha hb (by omega) (by omega)) w) =
    EvenImage.evenMap (unitData a b x y L) w
  apply EvenReindex.combination_reindex
  intro u
  rw [FiniteEvenSquareClasses.data, valueEquiv_apply_val]
  rfl

theorem unitClassMap_injective {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hprivate : FiniteEvenSquareClasses.Private (NormalizedWindowSets.union a b x y L)) :
    Function.Injective (unitClassMap a b x y L) := by
  intro u v heq
  apply (unitIntersectionEquiv ha hb hx hy hprivate).injective
  apply Subtype.ext
  rw [unitIntersectionEquiv_apply, unitIntersectionEquiv_apply]
  exact heq

end PaperP1.UnitIntersectionEquiv
