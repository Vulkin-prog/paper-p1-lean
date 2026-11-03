module

public import PaperP1.Asymptotics.TwoTargetWeakDenseCount
public import PaperP1.Asymptotics.TwoTargetWeakSingletonCount

/-! # Above half an effective window rank the literal weak-aligned pair population is subpower -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoTargetWeakUpperCount

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.PhysicalWindowRelations
  PaperP1.TwoTargetWindowSections PaperP1.TwoTargetClassOffsets PaperP1.TwoTargetPrimeClassSupports
  PaperP1.TwoTargetAllowedLabels PaperP1.TwoTargetUnitExclusion PaperP1.DisjointRecoverySubspace
  PaperP1.TwoTargetNonalignedDenseCount

local instance weakUpperPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
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
    (M : Submodule F₂ (code X L)) : DecidableEq (Module.Dual F₂ M) := Classical.decEq _

def HasSingleton {s : ℕ} (x : Fin s → ℕ) (L t k : ℕ) (j : Fin 2) (p : ℕ × ℕ) : Prop :=
  ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a ≤ (L + 1) ^ 3 ∧ b ≤ (L + 1) ^ 3 ∧
    EnlargedPairGeometry.Geometric a b p.1 p.2 L ∧ ∃ M : Submodule F₂ (code (starts x p.1 p.2) L),
    NoDisjointRecovery (CoordinateForms.coordinateFamily (code (starts x p.1 p.2) L)) M (s + 1) t ∧
    ∃ U : Finset (Fin (L + 1) × Fin (L + 1)), (NormalizedUnitCount.units a b p.1 p.2 L \ U).card ≤ 1 ∧
    ∃ c : ℕ, 0 < c ∧ ∃ α : Fin k → Module.Dual F₂ M, Function.Injective α ∧ (∀ i, α i ≠ 0) ∧
      (∀ i, α i ∉ excludedLabels (label (starts x p.1 p.2) M) U) ∧
      ∀ i, (targetOffsets (LabelClassPartition.part (label (starts x p.1 p.2) M) (α i)) j.rev).card = c ∧
        (targetOffsets (LabelClassPartition.part (label (starts x p.1 p.2) M) (α i)) j).card = 1

theorem uniform_pairs (s : ℕ) (C δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ t k : ℕ, 2 ≤ t ∧ 1 ≤ k ∧ (UniformOrdinarySurfaceCover.UniformCover k (t - 1) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k + 3) M) →
      ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ x : Fin s → ℕ, (∀ i, x i ∈ dyadicBlock N) →
      ∀ W : Submodule F₂ (ℕ →₀ F₂), W ≤ ⨆ i, squareClassSpace (x i) L →
      ∀ F : Finset (ℕ × ℕ), (∀ p ∈ F, p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N) →
        (∀ p ∈ F, CompressedTargetAlignment.Aligned 1 p.1 p.2 L ∧
          (Module.finrank F₂ ↥(squareClassSpace p.1 L ⊓ squareClassSpace p.2 L) : ℝ) ≤ (δ / 64) * L) →
        (∀ p ∈ F, Disjoint W (squareClassSpace p.1 L) ∧ Disjoint W (squareClassSpace p.2 L) ∧
          (1 / 2 + δ) * L ≤ (Module.finrank F₂ (Kernel p.1 p.2 L W) : ℝ)) →
        (F.card : ℝ) ≤ A * (N : ℝ) ^ ε) := by
  obtain ⟨t, ht, hregularize⟩ := TwoTargetWeakRegularization.uniform_selection_data s δ hδ
  obtain ⟨Nr, _hNr, hr⟩ := hregularize C
  obtain ⟨k, hk, hsingleton⟩ := TwoTargetWeakSingletonCount.uniform_hosts s t ht 1 C ε (by norm_num) hε
  obtain ⟨Np, _hNp, hpure⟩ := TwoTargetPureCount.uniform_pairs s t ht 1 C ε (by norm_num) hε
  obtain ⟨L₀, hL₀⟩ := exists_nat_gt (((t * k + 5 : ℕ) : ℝ) / δ)
  obtain ⟨Ng, hg⟩ := CriticalWindowGeometry.uniform_geometry C (L₀ + 1)
  refine ⟨t, k, ht, hk, ?_⟩
  intro hCover hPila
  obtain ⟨As, hAs, Ns, hs⟩ := hsingleton hCover hPila
  refine ⟨2 * As + 1, by positivity, max 3 (max Ns (max Np (max Ng Nr))), by omega, ?_⟩
  intro N hN L hband x hx W hW F hdyadic haligned hdense
  classical
  have hgeom := hg N (by omega) L hband
  have hL : 1 ≤ L := by omega
  have hlarge : ((t * k + 5 : ℕ) : ℝ) ≤ δ * L := by
    have hbase := (div_lt_iff₀ hδ).mp hL₀
    have hLL : (L₀ : ℝ) ≤ L := by exact_mod_cast (show L₀ ≤ L by omega)
    have hmono := mul_le_mul_of_nonneg_left hLL hδ.le
    nlinarith only [hbase, hmono]
  have hcases : ∀ p ∈ F, (∃ j : Fin 2, HasSingleton x L t k j p) ∨ HasPure x L t p := by
    intro p hp
    obtain ⟨hWY, hWZ, hdimR⟩ := hdense p hp
    obtain ⟨a, b, ha, hb, haH, hbH, hgeom, P, hno, hsize, U, _hUsub, _hUcard, hremaining, _hE, hpop⟩ :=
      hr N (by omega) L hL hband (δ / 64) (by positivity) x W hW p.1 p.2
        (hdyadic p hp).1 (hdyadic p hp).2 hWY hWZ (haligned p hp).1 (haligned p hp).2
    have hmany (j : Fin 2) : (t - 1 + 1) * k + 2 ≤
        (allowedSingletons (starts x p.1 p.2) P (excludedLabels (label (starts x p.1 p.2) P) U) j).card := by
      rw [show t - 1 + 1 = t by omega]
      have hb := (hpop j).2
      have heq : ((t * k + 5 : ℕ) : ℝ) = ((t * k + 2 : ℕ) : ℝ) + 3 := by push_cast; ring
      have h : ((t * k + 2 : ℕ) : ℝ) ≤
          (allowedSingletons (starts x p.1 p.2) P (excludedLabels (label (starts x p.1 p.2) P) U) j).card := by
        linarith only [hlarge, hb, hdimR, heq]
      exact_mod_cast h
    rcases TwoTargetAllowedSingletonSelection.singleton_dichotomy _ P _ (t - 1) k hk hsize hmany with hsingle | hpure
    · obtain ⟨j, hc⟩ := hsingle
      exact Or.inl ⟨j, a, b, ha, hb, haH, hbH, hgeom, P, hno, U, hremaining, hc⟩
    · apply Or.inr
      refine ⟨P, hno, ?_⟩
      intro j
      obtain ⟨α, hinj, hα, _hsafe, hdata⟩ := hpure j
      exact ⟨α, hinj, hα, hdata⟩
  let leftHosts := F.filter (HasSingleton x L t k 0)
  let rightHosts := F.filter (HasSingleton x L t k 1)
  let pureHosts := F.filter (HasPure x L t)
  have hsinglecount (j : Fin 2) : ((F.filter (HasSingleton x L t k j)).card : ℝ) ≤ As * (N : ℝ) ^ ε :=
    hs N (by omega) L (L + 1) hband le_rfl (by norm_num) x hx j _
      (fun p hp ↦ hdyadic p (mem_filter.mp hp).1)
      (fun _ hp ↦ (mem_filter.mp hp).2)
  have hpcount := hpure N (by omega) L (L + 1) hband le_rfl (by norm_num) x hx pureHosts
    (fun p hp ↦ hdyadic p (mem_filter.mp hp).1) (fun _ hp ↦ (mem_filter.mp hp).2)
  have hcover : F ⊆ (leftHosts ∪ rightHosts) ∪ pureHosts := by
    intro p hp
    rcases hcases p hp with ⟨j, hj⟩ | hpure
    · apply mem_union.mpr ∘ Or.inl
      fin_cases j
      · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨hp, hj⟩))
      · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨hp, hj⟩))
    · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨hp, hpure⟩))
  have hfinite : (F.card : ℝ) ≤ (leftHosts.card : ℝ) + rightHosts.card + pureHosts.card := by
    have h := (card_le_card hcover).trans ((card_union_le _ _).trans
      (Nat.add_le_add_right (card_union_le leftHosts rightHosts) pureHosts.card))
    exact_mod_cast h
  calc
    _ ≤ (leftHosts.card : ℝ) + rightHosts.card + pureHosts.card := hfinite
    _ ≤ As * (N : ℝ) ^ ε + As * (N : ℝ) ^ ε + (N : ℝ) ^ ε :=
      add_le_add (add_le_add (hsinglecount 0) (hsinglecount 1)) hpcount
    _ = _ := by ring

end PaperP1.TwoTargetWeakUpperCount
