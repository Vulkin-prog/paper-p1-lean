module

public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.Dimension.Localization

/-! # A genuine primitive coordinate forces the intermediate image ring to have the original fraction field -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimitiveBirationalFractionRing

theorem closure_eq_top {R B K L : Type*} [CommRing R] [CommRing B] [Field K] [Field L]
    [Algebra R B] [Algebra R K] [Algebra B L] [Algebra R L] [Algebra K L]
    [IsScalarTower R B L] [IsScalarTower R K L] [IsFractionRing R K]
    (γ : L) (hγ : ∃ b : B, algebraMap B L b = γ)
    (hprimitive : IntermediateField.adjoin K {γ} = ⊤) :
    Subfield.closure (Set.range (algebraMap B L)) = ⊤ := by
  let T := Subfield.closure (Set.range (algebraMap B L))
  have hR (a : R) : algebraMap R L a ∈ T := by
    rw [IsScalarTower.algebraMap_apply R B L]
    exact Subfield.subset_closure ⟨algebraMap R B a, rfl⟩
  have hK (k : K) : algebraMap K L k ∈ T := by
    obtain ⟨a, b, _hb, hfrac⟩ := IsFractionRing.div_surjective R k
    rw [← hfrac, map_div₀, ← IsScalarTower.algebraMap_apply R K L,
      ← IsScalarTower.algebraMap_apply R K L]
    exact T.div_mem (hR a) (hR b)
  have hγT : γ ∈ T := by
    obtain ⟨b, rfl⟩ := hγ
    exact Subfield.subset_closure ⟨b, rfl⟩
  have hall (z : L) : z ∈ T := by
    have hz : z ∈ IntermediateField.adjoin K {γ} := by rw [hprimitive]; trivial
    induction hz using IntermediateField.adjoin_induction with
    | mem z hz => exact (Set.mem_singleton_iff.mp hz).symm ▸ hγT
    | algebraMap k => exact hK k
    | add x y _hx _hy hx hy => exact T.add_mem hx hy
    | inv x _hx hx => exact T.inv_mem hx
    | mul x y _hx _hy hx hy => exact T.mul_mem hx hy
  exact top_unique (fun z _hz ↦ hall z)

theorem fraction_ring {R B K L : Type*} [CommRing R] [CommRing B] [Field K] [Field L]
    [Algebra R B] [Algebra R K] [Algebra B L] [Algebra R L] [Algebra K L]
    [IsScalarTower R B L] [IsScalarTower R K L] [IsFractionRing R K]
    (hbinj : Function.Injective (algebraMap B L))
    (γ : L) (hγ : ∃ b : B, algebraMap B L b = γ)
    (hprimitive : IntermediateField.adjoin K {γ} = ⊤) : IsFractionRing B L := by
  let : FaithfulSMul B L := (faithfulSMul_iff_algebraMap_injective B L).mpr hbinj
  let : IsDomain B := IsDomain.of_faithfulSMul B L
  let : Algebra (FractionRing B) L := FractionRing.liftAlgebra B L
  let : IsScalarTower B (FractionRing B) L := FractionRing.isScalarTower_liftAlgebra B L
  let f := IsScalarTower.toAlgHom B (FractionRing B) L
  have hcomp : (algebraMap (FractionRing B) L).comp (algebraMap B (FractionRing B)) = algebraMap B L :=
    (IsScalarTower.algebraMap_eq B (FractionRing B) L).symm
  have hrange : (algebraMap (FractionRing B) L).fieldRange = ⊤ := by
    rw [IsFractionRing.ringHom_fieldRange_eq_of_comp_eq hcomp]
    exact closure_eq_top (R := R) (K := K) γ hγ hprimitive
  have hsurj : Function.Surjective f := RingHom.fieldRange_eq_top_iff.mp hrange
  exact IsFractionRing.of_algEquiv (AlgEquiv.ofBijective f ⟨f.injective, hsurj⟩)

theorem rank_one {R B A K L : Type*} [CommRing R] [CommRing B] [CommRing A] [Field K] [Field L]
    [Algebra R B] [Algebra R K] [Algebra B A] [Algebra A L] [Algebra B L]
    [Algebra R L] [Algebra K L]
    [IsScalarTower R B L] [IsScalarTower R K L] [IsScalarTower B A L]
    [IsFractionRing R K] [IsFractionRing A L]
    (hbinj : Function.Injective (algebraMap B L))
    (γ : L) (hγ : ∃ b : B, algebraMap B L b = γ)
    (hprimitive : IntermediateField.adjoin K {γ} = ⊤) : Module.finrank B A = 1 := by
  let : IsFractionRing B L := fraction_ring (R := R) (K := K) hbinj γ hγ hprimitive
  have he := IsFractionRing.finrank_eq B L A L
  simpa only [Module.finrank_self] using he.symm

theorem normalization_rank {R B A K L : Type*} [CommRing R] [CommRing B] [CommRing A] [Field K] [Field L]
    [Algebra R B] [Algebra R A] [Algebra R K] [Algebra A L] [Algebra B L]
    [Algebra R L] [Algebra K L]
    [IsScalarTower R B L] [IsScalarTower R A L] [IsScalarTower R K L]
    [IsFractionRing R K] [IsFractionRing A L]
    (hbinj : Function.Injective (algebraMap B L))
    (γ : L) (hγ : ∃ b : B, algebraMap B L b = γ)
    (hprimitive : IntermediateField.adjoin K {γ} = ⊤) : Module.finrank R B = Module.finrank R A := by
  let : IsFractionRing B L := fraction_ring (R := R) (K := K) hbinj γ hγ hprimitive
  exact (IsFractionRing.finrank_left_eq R B L).trans (IsFractionRing.finrank_left_eq R A L).symm

end PaperP1.PrimitiveBirationalFractionRing
