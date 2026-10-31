module

public import Mathlib.Algebra.CharZero.Infinite
public import PaperP1.Diophantine.GeneralizedPell
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Norm
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.Trace.Basic


/-
Adapted from PaperC/Diophantine/HalterKochConductorDescent.lean, by Vulkin-prog, Apache-2.0.
Source commit b9fa9ba490f201b408a302a86f1594ee620b228b,
Git blob 6b970b5d96de14a796c4f0ec8fcd30cf3ebe2d11.
Concrete internally proved conductor descent only; historical stronger source interfaces excluded.
-/

@[expose] public section

namespace PaperP1.PellInput.QuadraticOrderConductor

open scoped NumberField
noncomputable section


open scoped QuadraticAlgebra

abbrev QD (D : ℕ) :=
  QuadraticAlgebra ℚ (D : ℚ) 0

section

variable (D : ℕ)
variable [Fact (∀ r : ℚ, r ^ 2 ≠ (D : ℚ) + 0 * r)]

local instance conductorNumberField : NumberField (QD D) :=
  NumberField.of_module_finite ℚ (QD D)

local instance conductorQuadraticExtension : Algebra.IsQuadraticExtension ℚ (QD D) where
  finrank_eq_two' := QuadraticAlgebra.finrank_eq_two _ _

theorem omega_sq :
    (⟨0, 1⟩ : QD D) ^ 2 = (D : QD D) := by
  ext <;> simp [pow_two]

theorem omega_integral :
    IsIntegral ℤ (⟨0, 1⟩ : QD D) := by
  apply IsIntegral.of_pow (n := 2) (by omega)
  rw [omega_sq]
  exact isIntegral_natCast D

def sqrtDO : NumberField.RingOfIntegers (QD D) :=
  ⟨⟨0, 1⟩, omega_integral D⟩

theorem sqrtDO_sq :
    (sqrtDO D) * (sqrtDO D) =
      (D : NumberField.RingOfIntegers (QD D)) := by
  apply NumberField.RingOfIntegers.ext
  change (⟨0, 1⟩ : QD D) * ⟨0, 1⟩ = (D : QD D)
  simpa only [pow_two] using omega_sq D

def embedOrder :
    ℤ√(D : ℤ) →+* NumberField.RingOfIntegers (QD D) :=
  Zsqrtd.lift ⟨sqrtDO D, sqrtDO_sq D⟩

theorem trace_eq (x : QD D) :
    Algebra.trace ℚ (QD D) x = 2 * x.re := by
  let b := QuadraticAlgebra.basis (D : ℚ) 0
  have hb0 : b 0 = (1 : QD D) := by
    apply b.repr.injective
    ext i
    fin_cases i <;> simp [b, QuadraticAlgebra.basis_repr_apply]
  have hb1 : b 1 = (⟨0, 1⟩ : QD D) := by
    apply b.repr.injective
    ext i
    fin_cases i <;> simp [b, QuadraticAlgebra.basis_repr_apply]
  rw [Algebra.trace_eq_matrix_trace b, Matrix.trace_fin_two]
  simp [Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply,
    b, QuadraticAlgebra.basis_repr_apply, hb0, hb1]
  ring

theorem norm_eq (x : QD D) :
    Algebra.norm ℚ x = x.re ^ 2 - (D : ℚ) * x.im ^ 2 := by
  rw [Algebra.norm_apply]
  change LinearMap.det
      (DistribSMul.toLinearMap ℚ (QD D) x) = _
  rw [QuadraticAlgebra.det_toLinearMap_eq_norm]
  simp [QuadraticAlgebra.norm_def]
  ring

abbrev OK := NumberField.RingOfIntegers (QD D)

omit [Fact (∀ r : ℚ, r ^ 2 ≠ (D : ℚ) + 0 * r)] in
theorem rat_eq_int_of_squarefree_mul_sq_eq_int
    (hDpos : 0 < D) (hDsquarefree : Squarefree D)
    (q : ℚ) (z : ℤ) (hz : (z : ℚ) = (D : ℚ) * q ^ 2) :
    ∃ b : ℤ, (b : ℚ) = q := by
  have hz0 : 0 ≤ z := by
    exact_mod_cast (show (0 : ℚ) ≤ z by rw [hz]; positivity)
  let n : ℕ := z.natAbs
  have hnz : (n : ℤ) = z := Int.natAbs_of_nonneg hz0
  have hnq : (n : ℚ) = (D : ℚ) * q ^ 2 := by
    rw [← hz]
    exact_mod_cast hnz
  have hsquareQ : IsSquare ((D * n : ℕ) : ℚ) := by
    refine ⟨(D : ℚ) * q, ?_⟩
    rw [Nat.cast_mul, hnq]
    ring
  have hsquareNat : IsSquare (D * n) :=
    Rat.isSquare_natCast_iff.mp hsquareQ
  obtain ⟨k, hk⟩ := hsquareNat
  have hDdvdKsq : D ∣ k ^ 2 := by
    refine ⟨n, ?_⟩
    simpa only [pow_two] using hk.symm
  have hDdvdK : D ∣ k :=
    (hDsquarefree.dvd_pow_iff_dvd (by decide)).mp hDdvdKsq
  obtain ⟨l, rfl⟩ := hDdvdK
  have hn : n = D * l ^ 2 := by
    have hk' : D * n = D * (D * l ^ 2) := by
      simpa only [pow_two] using (hk.trans (by ring))
    exact Nat.eq_of_mul_eq_mul_left hDpos hk'
  have hq : q ^ 2 = (l : ℚ) ^ 2 := by
    rw [hn] at hnq
    push_cast at hnq
    apply mul_left_cancel₀ (show (D : ℚ) ≠ 0 by positivity)
    simpa only [mul_assoc] using hnq.symm
  rcases eq_or_eq_neg_of_sq_eq_sq q (l : ℚ) hq with h | h
  · exact ⟨l, h.symm⟩
  · exact ⟨-(l : ℤ), by exact_mod_cast h.symm⟩

theorem two_mul_mem_order
    (hDpos : 0 < D) (hDsquarefree : Squarefree D)
    (z : OK D) :
    ∃ a : ℤ√(D : ℤ), embedOrder D a = (2 : OK D) * z := by
  have htraceInt :
      IsIntegral ℤ (Algebra.trace ℚ (QD D) (z : QD D)) :=
    Algebra.isIntegral_trace z.property
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp htraceInt
  have ha' : (a : ℚ) = 2 * (z : QD D).re := by
    simpa [trace_eq D] using ha
  have hnormInt :
      IsIntegral ℤ (Algebra.norm ℚ (z : QD D)) :=
    Algebra.isIntegral_norm ℚ z.property
  obtain ⟨c, hc⟩ := IsIntegrallyClosed.isIntegral_iff.mp hnormInt
  have hc' : (c : ℚ) =
      (z : QD D).re ^ 2 - (D : ℚ) * (z : QD D).im ^ 2 := by
    simpa [norm_eq D] using hc
  let w : ℤ := a ^ 2 - 4 * c
  have hw : (w : ℚ) = (D : ℚ) * (2 * (z : QD D).im) ^ 2 := by
    dsimp [w]
    push_cast
    rw [ha', hc']
    ring
  obtain ⟨b, hb⟩ :=
    rat_eq_int_of_squarefree_mul_sq_eq_int D hDpos hDsquarefree
      (2 * (z : QD D).im) w hw
  refine ⟨⟨a, b⟩, ?_⟩
  apply NumberField.RingOfIntegers.ext
  change (a : QD D) + (b : QD D) * (⟨0, 1⟩ : QD D) =
    (2 : QD D) * (z : QD D)
  apply QuadraticAlgebra.ext
  · simpa using ha'
  · simpa using hb

def alphaO (s : ℤ × ℤ) : OK D :=
  embedOrder D (toZsqrtd D s)

def betaO (s : ℤ × ℤ) : OK D :=
  embedOrder D (star (toZsqrtd D s))

theorem alphaO_mul_betaO {M : ℤ} {s : ℤ × ℤ}
    (hs : s.1 ^ 2 - (D : ℤ) * s.2 ^ 2 = M) :
    alphaO D s * betaO D s = (M : OK D) := by
  rw [alphaO, betaO, ← map_mul, ← Zsqrtd.norm_eq_mul_conj,
    generalizedPellEquation_iff_norm.mp hs]
  exact map_intCast (embedOrder D) M

def idealOf (M : ℤ) (s : ℤ × ℤ) :
    {I : Ideal (OK D) //
      I ∣ Ideal.span ({(M : OK D)} : Set (OK D))} := by
  by_cases hs : s.1 ^ 2 - (D : ℤ) * s.2 ^ 2 = M
  · refine ⟨Ideal.span ({alphaO D s} : Set (OK D)), ?_⟩
    refine ⟨Ideal.span ({betaO D s} : Set (OK D)), ?_⟩
    rw [Ideal.span_singleton_mul_span_singleton, alphaO_mul_betaO D hs]
  · refine ⟨⊤, ?_⟩
    refine ⟨Ideal.span ({(M : OK D)} : Set (OK D)), ?_⟩
    simp

theorem embedOrder_injective :
    Function.Injective (embedOrder D) := by
  apply Zsqrtd.lift_injective
  intro n hn
  apply (Fact.out : ∀ r : ℚ, r ^ 2 ≠ (D : ℚ) + 0 * r) (n : ℚ)
  norm_num [pow_two]
  exact_mod_cast hn.symm

def twoIdeal : Ideal (OK D) :=
  Ideal.span {((2 : ℕ) : OK D)}

theorem twoIdeal_ne_bot : twoIdeal D ≠ ⊥ := by
  apply mt Ideal.span_singleton_eq_bot.mp
  norm_num

theorem twoQuotient_natCard :
    Nat.card (OK D ⧸ twoIdeal D) = 4 := by
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  rw [twoIdeal, Ideal.absNorm_span_natCast,
    NumberField.RingOfIntegers.rank]
  rw [Algebra.IsQuadraticExtension.finrank_eq_two]
  norm_num

noncomputable local instance twoQuotientFintype :
    Fintype (OK D ⧸ twoIdeal D) := by
  let : Finite (OK D ⧸ twoIdeal D) :=
    Ring.HasFiniteQuotients.finiteQuotient (twoIdeal_ne_bot D)
  exact Fintype.ofFinite _

theorem twoQuotient_card :
    Fintype.card (OK D ⧸ twoIdeal D) = 4 := by
  rw [← Nat.card_eq_fintype_card]
  exact twoQuotient_natCard D

noncomputable def residueEquivFinFour :
    (OK D ⧸ twoIdeal D) ≃ Fin 4 :=
  (Fintype.equivFin _).trans (finCongr (twoQuotient_card D))

theorem mem_twoIdeal_iff (x : OK D) :
    x ∈ twoIdeal D ↔ ∃ y : OK D, (2 : OK D) * y = x := by
  rw [twoIdeal, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, by simpa [mul_comm] using hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, by simpa [mul_comm] using hy⟩

theorem mem_embedOrder_of_sub_one_mem_twoIdeal
    (x : OK D) (hx : x - 1 ∈ twoIdeal D)
    (hDpos : 0 < D) (hDsquarefree : Squarefree D) :
    ∃ a : ℤ√(D : ℤ), embedOrder D a = x := by
  obtain ⟨y, hy⟩ := (mem_twoIdeal_iff D (x - 1)).mp hx
  obtain ⟨a, ha⟩ := two_mul_mem_order D hDpos hDsquarefree y
  refine ⟨a + 1, ?_⟩
  rw [map_add, map_one, ha, hy]
  exact sub_add_cancel x 1

theorem unit_mem_embedOrder_of_mod_two_eq_one
    (u : (OK D)ˣ)
    (hu : Ideal.Quotient.mk (twoIdeal D) (u : OK D) = 1)
    (hDpos : 0 < D) (hDsquarefree : Squarefree D) :
    ∃ v : (ℤ√(D : ℤ))ˣ, Units.map (embedOrder D) v = u := by
  have huMem : (u : OK D) - 1 ∈ twoIdeal D := by
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem
      (u : OK D) 1).mp (by simpa using hu)
  obtain ⟨a, ha⟩ := mem_embedOrder_of_sub_one_mem_twoIdeal D
    (u : OK D) huMem hDpos hDsquarefree
  have huInv :
      Ideal.Quotient.mk (twoIdeal D) ((u⁻¹ : (OK D)ˣ) : OK D) = 1 := by
    let qhom : OK D →+* (OK D ⧸ twoIdeal D) :=
      Ideal.Quotient.mk (twoIdeal D)
    have huUnits : Units.map qhom.toMonoidHom u = 1 := by
      apply Units.ext
      exact hu
    have huInvUnits : Units.map qhom.toMonoidHom (u⁻¹) = 1 := by
      simpa using congrArg Inv.inv huUnits
    exact congrArg Units.val huInvUnits
  have huInvMem : ((u⁻¹ : (OK D)ˣ) : OK D) - 1 ∈ twoIdeal D := by
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem
      ((u⁻¹ : (OK D)ˣ) : OK D) 1).mp (by simpa using huInv)
  obtain ⟨b, hb⟩ := mem_embedOrder_of_sub_one_mem_twoIdeal D
    ((u⁻¹ : (OK D)ˣ) : OK D) huInvMem hDpos hDsquarefree
  have hab : a * b = 1 := by
    apply embedOrder_injective D
    rw [map_mul, ha, hb]
    simp
  have hba : b * a = 1 := by rw [mul_comm, hab]
  let v : (ℤ√(D : ℤ))ˣ := ⟨a, b, hab, hba⟩
  refine ⟨v, ?_⟩
  apply Units.ext
  exact ha

def Solution (M : ℤ) :=
  {s : ℤ × ℤ // s.1 ^ 2 - (D : ℤ) * s.2 ^ 2 = M}

def solutionIdeal (M : ℤ) (s : Solution D M) : Ideal (OK D) :=
  Ideal.span ({alphaO D s.1} : Set (OK D))

def solutionIdealSetoid (M : ℤ) : Setoid (Solution D M) where
  r s t := solutionIdeal D M s = solutionIdeal D M t
  iseqv := ⟨fun _ ↦ rfl, fun h ↦ h.symm, fun h₁ h₂ ↦ h₁.trans h₂⟩

noncomputable def solutionRepresentative
    (M : ℤ) (s : Solution D M) : Solution D M :=
  Quotient.out (Quotient.mk (solutionIdealSetoid D M) s)

theorem solutionRepresentative_ideal
    (M : ℤ) (s : Solution D M) :
    solutionIdeal D M (solutionRepresentative D M s) =
      solutionIdeal D M s := by
  exact Quotient.exact (Quotient.out_eq
    (Quotient.mk (solutionIdealSetoid D M) s))

noncomputable def relativeUnit
    (M : ℤ) (s : Solution D M) : (OK D)ˣ :=
  Classical.choose
    (Ideal.span_singleton_eq_span_singleton.mp
      (solutionRepresentative_ideal D M s))

theorem relativeUnit_spec (M : ℤ) (s : Solution D M) :
    alphaO D (solutionRepresentative D M s).1 *
        (relativeUnit D M s : OK D) = alphaO D s.1 := by
  exact Classical.choose_spec
    (Ideal.span_singleton_eq_span_singleton.mp
      (solutionRepresentative_ideal D M s))

noncomputable def solutionColour
    (M : ℤ) (s : Solution D M) : Fin 4 :=
  residueEquivFinFour D
    (Ideal.Quotient.mk (twoIdeal D) (relativeUnit D M s : OK D))

noncomputable def conductorColour
    (M : ℤ) (s : ℤ × ℤ) : Fin 4 :=
  if hs : s.1 ^ 2 - (D : ℤ) * s.2 ^ 2 = M then
    solutionColour D M ⟨s, hs⟩
  else 0

theorem same_principalIdeal_of_same_extension
    (M : ℤ) (hDpos : 0 < D) (hDsquarefree : Squarefree D)
    (s t : ℤ × ℤ)
    (hs : s.1 ^ 2 - (D : ℤ) * s.2 ^ 2 = M)
    (ht : t.1 ^ 2 - (D : ℤ) * t.2 ^ 2 = M)
    (hcolour : conductorColour D M s = conductorColour D M t)
    (hideal : idealOf D M s = idealOf D M t) :
    Ideal.span ({toZsqrtd D s} : Set (ℤ√(D : ℤ))) =
      Ideal.span ({toZsqrtd D t} : Set (ℤ√(D : ℤ))) := by
  let ss : Solution D M := ⟨s, hs⟩
  let tt : Solution D M := ⟨t, ht⟩
  have hideal' : solutionIdeal D M ss = solutionIdeal D M tt := by
    have h := congrArg Subtype.val hideal
    simpa [ss, tt, idealOf, solutionIdeal, hs, ht] using h
  have hclass :
      Quotient.mk (solutionIdealSetoid D M) ss =
        Quotient.mk (solutionIdealSetoid D M) tt :=
    Quotient.sound hideal'
  have hrep :
      solutionRepresentative D M ss = solutionRepresentative D M tt := by
    exact congrArg Quotient.out hclass
  have hcolour' : solutionColour D M ss = solutionColour D M tt := by
    simpa [conductorColour, hs, ht, ss, tt] using hcolour
  have hresidue :
      Ideal.Quotient.mk (twoIdeal D) (relativeUnit D M ss : OK D) =
        Ideal.Quotient.mk (twoIdeal D) (relativeUnit D M tt : OK D) := by
    exact (residueEquivFinFour D).injective hcolour'
  let us : (OK D)ˣ := relativeUnit D M ss
  let ut : (OK D)ˣ := relativeUnit D M tt
  let w : (OK D)ˣ := us⁻¹ * ut
  have hwmod : Ideal.Quotient.mk (twoIdeal D) (w : OK D) = 1 := by
    let rho : OK D →+* (OK D ⧸ twoIdeal D) :=
      Ideal.Quotient.mk (twoIdeal D)
    have hUnits :
        Units.map rho.toMonoidHom us = Units.map rho.toMonoidHom ut := by
      apply Units.ext
      exact hresidue
    have hwUnits : Units.map rho.toMonoidHom w = 1 := by
      dsimp [w]
      simp only [map_mul, map_inv]
      calc
        (Units.map rho.toMonoidHom us)⁻¹ * Units.map rho.toMonoidHom ut =
            (Units.map rho.toMonoidHom ut)⁻¹ *
              Units.map rho.toMonoidHom ut :=
          congrArg (fun x ↦ x⁻¹ * Units.map rho.toMonoidHom ut) hUnits
        _ = 1 := by simp
    exact congrArg Units.val hwUnits
  obtain ⟨v, hv⟩ :=
    unit_mem_embedOrder_of_mod_two_eq_one D w hwmod
      hDpos hDsquarefree
  have hwRel : alphaO D s * (w : OK D) = alphaO D t := by
    calc
      alphaO D s * (w : OK D) =
          (alphaO D (solutionRepresentative D M ss).1 * (us : OK D)) *
            ((us⁻¹ : (OK D)ˣ) : OK D) * (ut : OK D) := by
              rw [relativeUnit_spec D M ss]
              simp [w, ss, us, ut, mul_assoc]
      _ = alphaO D (solutionRepresentative D M ss).1 * (ut : OK D) := by
            simp [mul_assoc]
      _ = alphaO D (solutionRepresentative D M tt).1 * (ut : OK D) := by
            rw [hrep]
      _ = alphaO D t := relativeUnit_spec D M tt
  have hvVal : embedOrder D (v : ℤ√(D : ℤ)) = (w : OK D) := by
    exact congrArg Units.val hv
  have horderRel :
      toZsqrtd D s * (v : ℤ√(D : ℤ)) = toZsqrtd D t := by
    apply embedOrder_injective D
    rw [map_mul, hvVal]
    exact hwRel
  apply le_antisymm
  · rw [Ideal.span_singleton_le_span_singleton]
    refine ⟨(v⁻¹ : (ℤ√(D : ℤ))ˣ), ?_⟩
    calc
      toZsqrtd D s =
          (toZsqrtd D s * (v : ℤ√(D : ℤ))) *
            ((v⁻¹ : (ℤ√(D : ℤ))ˣ) : ℤ√(D : ℤ)) := by
              simp [mul_assoc]
      _ = toZsqrtd D t *
            ((v⁻¹ : (ℤ√(D : ℤ))ˣ) : ℤ√(D : ℤ)) := by
              rw [horderRel]
  · rw [Ideal.span_singleton_le_span_singleton]
    exact ⟨v, horderRel.symm⟩

noncomputable def conductorData
    (M : ℤ) (hDpos : 0 < D) (hDsquarefree : Squarefree D) :
    QuadraticOrderConductorData D M where
  K := QD D
  idealOf := idealOf D M
  conductorColour := conductorColour D M
  same_principalIdeal_of_same_extension :=
    same_principalIdeal_of_same_extension D M hDpos hDsquarefree

end

/--
The quadratic-order conductor fibre bound, constructed entirely in Lean.

The proof uses the four residue classes of `O_K / 2 O_K`; it therefore proves
the historical `Fin 4` interface directly and does not assume the stronger
source-shaped three-unit-coset record.
-/
theorem quadraticOrderConductorFiberBoundInternal :
    QuadraticOrderConductorFiberBoundStatement := by
  intro D M hDpos hDsquarefree hDnonsquare _hM
  let : Fact (∀ r : ℚ, r ^ 2 ≠ (D : ℚ) + 0 * r) := ⟨by
    intro r hr
    apply hDnonsquare
    refine ⟨r, ?_⟩
    simpa [pow_two] using hr.symm⟩
  exact ⟨conductorData D M hDpos hDsquarefree⟩


end

end PaperP1.PellInput.QuadraticOrderConductor

