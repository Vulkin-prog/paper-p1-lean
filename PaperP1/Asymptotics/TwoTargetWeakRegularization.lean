module

public import PaperP1.Asymptotics.WeakAlignmentUnitCount
public import PaperP1.Arithmetic.TwoTargetAllowedSingletonSelection
public import PaperP1.Arithmetic.TwoTargetUnitExclusion
public import PaperP1.Arithmetic.CompressedTargetAlignment

/-! # Uniform weak-alignment exclusions preserve both actual target populations on one physical relation space -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoTargetWeakRegularization

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.PhysicalWindowRelations
  PaperP1.TwoTargetWindowSections PaperP1.TwoTargetPrimeClassSupports PaperP1.DisjointRecoverySubspace
  PaperP1.TwoTargetAllowedLabels PaperP1.TwoTargetUnitExclusion PaperP1.NormalizedUnitCount

local instance weakRegularizationPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) : Module F₂ S := S.module
local instance kernelAddCommGroup {y z L : ℕ} (W : Submodule F₂ (ℕ →₀ F₂)) :
    AddCommGroup (Kernel y z L W) := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := W × squareClassSpace y L × squareClassSpace z L) (Kernel y z L W)
local instance codeAddCommGroup {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) : AddCommGroup (code X L) := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := ((Fin s ⊕ Fin 2) × Fin (L + 1)) → F₂) (code X L)
local instance physicalAddCommGroup {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ)
    (P : Submodule F₂ (code X L)) : AddCommGroup P := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := code X L) P
local instance dualDecidableEq {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ)
    (P : Submodule F₂ (code X L)) : DecidableEq (Module.Dual F₂ P) := Classical.decEq _

theorem excluded_budget {s L : ℕ} {A : Type*} [DecidableEq A]
    (ℓ : TwoTargetWindowSections.Coordinate s L → A)
    (U D : Finset (Fin (L + 1) × Fin (L + 1))) (θ : ℝ) (hθ : 0 ≤ θ)
    (hD : D.card = U.card - 1) (hU : (U.card : ℝ) ≤ θ * L + 2) :
    ((excludedLabels ℓ D).card : ℝ) ≤ 2 * θ * L + 2 := by
  have hE : ((excludedLabels ℓ D).card : ℝ) ≤ 2 * (D.card : ℝ) := by
    exact_mod_cast image_labels_card ℓ D
  have hθL : 0 ≤ θ * L := mul_nonneg hθ (Nat.cast_nonneg L)
  by_cases hu : 1 ≤ U.card
  · have hd : (D.card : ℝ) = U.card - 1 := by rw [hD, Nat.cast_sub hu]; norm_num
    linarith only [hE, hd, hU]
  · have hd : D.card = 0 := by omega
    rw [hd, Nat.cast_zero, mul_zero] at hE
    linarith only [hE, hθL]

theorem population_bounds {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (P : Submodule F₂ (code X L))
    (hinj : ∀ j : Fin 2, Function.Injective ((projection X L (Sum.inr j)).comp P.subtype))
    (E : Finset (Module.Dual F₂ P)) (d ξ θ : ℝ)
    (hdim : d - ξ * L / 4 ≤ Module.finrank F₂ P)
    (hE : (E.card : ℝ) ≤ 2 * θ * L + 2) (j : Fin 2) :
    d - ξ * L / 4 - (2 * θ * L + 2) ≤ (allowedLabels X P E j).card ∧
      2 * d - ξ * L / 2 - (L + 1) - (2 * θ * L + 2) ≤ (allowedSingletons X P E j).card := by
  have ht : (Module.finrank F₂ P : ℝ) ≤ (allowedLabels X P E j).card + (E.card : ℝ) := by
    exact_mod_cast (TwoTargetLabelDimension.dimension_le_labels X P hinj j).trans
      (target_population_budget X P E j)
  have hs : 2 * (Module.finrank F₂ P : ℝ) ≤ (L + 1 : ℕ) +
      ((allowedSingletons X P E j).card + (E.card : ℝ)) := by
    exact_mod_cast (TwoTargetSingletonLabels.dimension_singleton_budget X P hinj j).trans
      (Nat.add_le_add_left (singleton_population_budget X P E j) (L + 1))
  push_cast at hs
  constructor <;> linarith only [ht, hs, hdim, hE]

theorem uniform_selection_data (s : ℕ) (ξ : ℝ) (hξ : 0 < ξ) :
    ∃ t : ℕ, 2 ≤ t ∧ ∀ C : ℝ, ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ, 1 ≤ L →
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ θ : ℝ, 0 ≤ θ → ∀ x : Fin s → ℕ,
      ∀ W : Submodule F₂ (ℕ →₀ F₂), W ≤ ⨆ i, squareClassSpace (x i) L →
      ∀ y z : ℕ, y ∈ dyadicBlock N → z ∈ dyadicBlock N →
      Disjoint W (squareClassSpace y L) → Disjoint W (squareClassSpace z L) →
      CompressedTargetAlignment.Aligned 1 y z L →
      (Module.finrank F₂ ↥(squareClassSpace y L ⊓ squareClassSpace z L) : ℝ) ≤ θ * L →
      ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a ≤ (L + 1) ^ 3 ∧ b ≤ (L + 1) ^ 3 ∧
        EnlargedPairGeometry.Geometric a b y z L ∧
      ∃ P : Submodule F₂ (code (starts x y z) L),
        NoDisjointRecovery (CoordinateForms.coordinateFamily (code (starts x y z) L)) P (s + 1) t ∧
        (∀ α : Module.Dual F₂ P, α ≠ 0 → (LabelClassPartition.part (label (starts x y z) P) α).card ≤ t - 1) ∧
      ∃ D : Finset (Fin (L + 1) × Fin (L + 1)), D ⊆ units a b y z L ∧
        D.card = (units a b y z L).card - 1 ∧ (units a b y z L \ D).card ≤ 1 ∧
        ((excludedLabels (label (starts x y z) P) D).card : ℝ) ≤ 2 * θ * L + 2 ∧
        ∀ j : Fin 2,
          (Module.finrank F₂ (Kernel y z L W) : ℝ) - ξ * L / 4 - (2 * θ * L + 2) ≤
            (allowedLabels (starts x y z) P (excludedLabels (label (starts x y z) P) D) j).card ∧
          2 * (Module.finrank F₂ (Kernel y z L W) : ℝ) - ξ * L / 2 - (L + 1) - (2 * θ * L + 2) ≤
            (allowedSingletons (starts x y z) P (excludedLabels (label (starts x y z) P) D) j).card := by
  obtain ⟨t, ht, hregularize⟩ := TwoTargetPhysicalRegularization.uniform_physical_subspace s ξ hξ
  refine ⟨t, ht, ?_⟩
  intro C
  obtain ⟨N₀, hN₀, hu⟩ := WeakAlignmentUnitCount.uniform_weak_bound C
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hL hband θ hθ x W hW y z hy hz hWY hWZ halign hweak
  obtain ⟨a, b, ha, hb, _hcop, haH, hbH, hab⟩ := halign
  have hgeom : EnlargedPairGeometry.Geometric a b y z L := by
    simpa only [EnlargedPairGeometry.Geometric, one_mul, abs_sub_comm] using hab
  obtain ⟨P, hno, hdim, hinj⟩ := hregularize x y z L hL W hW hWY hWZ
  have hsize (α : Module.Dual F₂ P) (hα : α ≠ 0) :
      (LabelClassPartition.part (label (starts x y z) P) α).card ≤ t - 1 :=
    coordinate_multiplicity_le (CoordinateForms.coordinateFamily (code (starts x y z) L)) P
      (s + 1) t (by omega) hno α hα
  obtain ⟨D, hDsub, hDcard, hremaining⟩ := except_one (units a b y z L)
  have hE := excluded_budget (label (starts x y z) P) (units a b y z L) D θ hθ hDcard
    (hu N hN L hband y z hy hz θ hweak a b ha hb)
  exact ⟨a, b, ha, hb, haH, hbH, hgeom, P, hno, hsize, D, hDsub, hDcard, hremaining,
    hE, population_bounds _ P hinj _ _ ξ θ hdim hE⟩

end PaperP1.TwoTargetWeakRegularization
