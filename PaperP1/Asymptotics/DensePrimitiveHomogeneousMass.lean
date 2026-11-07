module

public import PaperP1.Asymptotics.PrimitiveTripleMass
public import PaperP1.Asymptotics.HomogeneousLocalMarginalCap
public import PaperP1.Asymptotics.HalfCountSchedule

/-! # The actual homogeneous mass of dense primitive triples

Every homogeneous local probability is capped using the proved local
rigidity theorem. Exact homogeneous factorization and primitive relative
nullity then give a uniform O(N^-2) point bound, including irregular
windows. The internally proved dense host count yields the printed
N^(-2+epsilon) total homogeneous mass, without affine compatibility or
nonzero original marginals. The final endpoint retains all three clauses
of companion T8.2.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace PaperP1.DensePrimitiveHomogeneousMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.ConnectedWindowFamilies

local instance homogeneousDensePrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

def mass (F : Finset (Finset ℕ)) (L : ℕ) : ℝ :=
  ∑ I ∈ F, HomogeneousRunMass.probability L I

def constant (C : ℝ) : ℝ := 8*((2 : ℝ)^C)^4

theorem two_pow_upper {N L : ℕ} {C : ℝ} (hN : 2 ≤ N)
    (hband : |(L : ℝ)-Real.log N/Real.log 2| ≤ C) :
    (2^L : ℝ) ≤ (N : ℝ)*(2 : ℝ)^C := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : (L : ℝ) ≤ Real.log N/Real.log 2+C := by
    have h := (abs_le.mp hband).2
    linarith
  have hlog := mul_le_mul_of_nonneg_right hL h2.le
  rw [add_mul, div_mul_cancel₀ _ h2.ne'] at hlog
  have he := Real.exp_le_exp.mpr hlog
  rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ)<2),
    Real.exp_add, Real.exp_log hn] at he
  have hc : Real.exp (C*Real.log 2) = (2 : ℝ)^C := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ)<2), mul_comm C (Real.log 2)]
  rw [hc] at he
  exact he

theorem uniform_point_bound (C : ℝ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C → ∀ I : Finset ℕ,
      I ⊆ dyadicBlock N → I.card = 3 → Primitive L I →
      HomogeneousRunMass.probability L I ≤ constant C/(N : ℝ)^2 := by
  obtain ⟨N₀,hN₀,hcap⟩ := HomogeneousLocalMarginalCap.uniform_cap C
  refine ⟨N₀,hN₀,?_⟩
  intro N hN L hband I hI hcard hprim
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hne : I.Nonempty := card_pos.mp (by rw [hcard]; norm_num)
  have hpos : ∀ x ∈ I, 0 < x := by
    intro x hx
    have hh := (mem_Ico.mp (hI hx)).1
    omega
  have hr := PrimitiveWindowMass.primitive_nullity_le L I hne hprim hpos
  have hp : (2^relativeNullityOn (fun x ↦ squareClassSpace x L) I : ℝ) ≤ 2^L := by
    gcongr; norm_num
  have hprod : (∏ x ∈ I, HomogeneousRunMass.probability L {x}) ≤
      (2*(2 : ℝ)^C/N)^3 := by
    calc
      _ ≤ ∏ _x ∈ I, 2*(2 : ℝ)^C/N := prod_le_prod₀
        (fun x _ ↦ (HomogeneousRunMass.probability_pos L {x}).le)
        (fun x hx ↦ hcap N hN L hband x (hI hx))
      _ = _ := by rw [prod_const, hcard]
  rw [HomogeneousEffectiveWeights.factor]
  calc
    _ ≤ (2*(2 : ℝ)^C/N)^3*(2^L : ℝ) :=
      mul_le_mul hprod hp (by positivity) (by positivity)
    _ ≤ (2*(2 : ℝ)^C/N)^3*((N : ℝ)*(2 : ℝ)^C) :=
      mul_le_mul_of_nonneg_left (two_pow_upper (by omega) hband) (by positivity)
    _ = _ := by unfold constant; field_simp; ring

theorem uniform_mass (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ I.card = 3 ∧ Primitive L I ∧
        η*((L+1 : ℕ) : ℝ) ≤ (runRelativeNullity L I : ℝ)) →
      mass F L ≤ (N : ℝ)^(-2+ε) := by
  obtain ⟨NH,_hNH,hh⟩ := DensePrimitiveTripleHosts.companion_T8_2_hosts C η (ε/2) hη (by positivity)
  obtain ⟨NP,_hNP,hp⟩ := uniform_point_bound C
  obtain ⟨NA,ha⟩ := HalfCountSchedule.factor_absorption (constant C) (-2+ε/2) (ε/2) (by positivity)
  refine ⟨3+NH+NP+NA,by omega,?_⟩
  intro N hN L hband F hF
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hc : (F.card : ℝ) ≤ (N : ℝ)^(ε/2) := hh N (by omega) L hband F (by
    intro I hIF
    obtain ⟨hI,hcard,hprim,hdense⟩ := hF I hIF
    exact ⟨hcard,hI,hprim,hdense⟩)
  have hk : 0 ≤ constant C/(N : ℝ)^2 := by unfold constant; positivity
  have hneg : (N : ℝ)^(-2 : ℝ) = ((N : ℝ)^2)⁻¹ := by
    rw [Real.rpow_neg hn.le, Real.rpow_two]
  calc
    _ ≤ ∑ _I ∈ F, constant C/(N : ℝ)^2 := by
      apply sum_le_sum
      intro I hIF
      exact hp N (by omega) L hband I (hF I hIF).1 (hF I hIF).2.1 (hF I hIF).2.2.1
    _ = (F.card : ℝ)*(constant C/(N : ℝ)^2) := by simp
    _ ≤ (N : ℝ)^(ε/2)*(constant C/(N : ℝ)^2) := mul_le_mul_of_nonneg_right hc hk
    _ = constant C*(N : ℝ)^(-2+ε/2) := by rw [Real.rpow_add hn, hneg]; ring
    _ ≤ (N : ℝ)^((-2+ε/2)+ε/2) := ha N (by omega)
    _ = _ := by congr 1; ring

theorem companion_T8_2 (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      (∀ F : Finset (Finset ℕ),
        (∀ I ∈ F, I ⊆ dyadicBlock N ∧ I.card = 3 ∧ Primitive L I ∧
          η*((L+1 : ℕ) : ℝ) ≤ (runRelativeNullity L I : ℝ)) →
        (F.card : ℝ) ≤ (N : ℝ)^ε ∧ mass F L ≤ (N : ℝ)^(-2+ε)) ∧
      (∀ F : Finset (Finset ℕ),
        (∀ I ∈ F, I ⊆ dyadicBlock N ∧ I.card = 3 ∧ Primitive L I) →
        (∑ I ∈ F, |infiniteCenteredCoefficient L I|) ≤ (N : ℝ)^(-(3 : ℝ)/2+ε)) := by
  obtain ⟨NO,_hNO,ho⟩ := PrimitiveTripleMass.companion_T8_2 C η ε hη hε
  obtain ⟨NH,_hNH,hh⟩ := uniform_mass C η ε hη hε
  refine ⟨3+NO+NH,by omega,?_⟩
  intro N hN L hband
  have hold := ho N (by omega) L hband
  exact ⟨fun F hF ↦ ⟨(hold.1 F hF).1,hh N (by omega) L hband F hF⟩,hold.2⟩

end PaperP1.DensePrimitiveHomogeneousMass
