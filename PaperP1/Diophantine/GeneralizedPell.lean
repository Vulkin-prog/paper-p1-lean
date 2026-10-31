module

public import PaperP1.Diophantine.PellInput
public import PaperP1.Diophantine.QuadraticIdealDivisors
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.NumberTheory.Pell

/-! Ideal, unit-orbit, height and squarefree-reduction proofs for P1 T1.2. -/

/-
Adapted from PaperC/Diophantine/GeneralizedPell.lean, by Vulkin-prog, Apache-2.0.
Source commit b9fa9ba490f201b408a302a86f1594ee620b228b,
Git blob 19a257299fe1f2d0223a16fa3cdc938fbf0e142b.
Finite ideal/unit/height and squarefree reduction only; Nicolas--Robin predicate and final conditional theorem excluded.
-/

@[expose] public section

namespace PaperP1.PellInput

open scoped NumberField Pointwise

/-- The element `x + y √D` attached to an integral pair. -/
def toZsqrtd (D : ℕ) (s : ℤ × ℤ) : ℤ√(D : ℤ) :=
  ⟨s.1, s.2⟩

@[simp]
theorem toZsqrtd_re (D : ℕ) (s : ℤ × ℤ) :
    (toZsqrtd D s).re = s.1 :=
  rfl

@[simp]
theorem toZsqrtd_im (D : ℕ) (s : ℤ × ℤ) :
    (toZsqrtd D s).im = s.2 :=
  rfl

/-- The generalized Pell equation is exactly the `Zsqrtd` norm equation. -/
theorem norm_toZsqrtd (D : ℕ) (s : ℤ × ℤ) :
    (toZsqrtd D s).norm =
      s.1 ^ 2 - (D : ℤ) * s.2 ^ 2 := by
  simp only [toZsqrtd, Zsqrtd.norm_def]
  ring

theorem generalizedPellEquation_iff_norm
    {D : ℕ} {M : ℤ} {s : ℤ × ℤ} :
    s.1 ^ 2 - (D : ℤ) * s.2 ^ 2 = M ↔
      (toZsqrtd D s).norm = M := by
  rw [norm_toZsqrtd]

/-!
## The narrow order/maximal-order comparison

The manuscript sends a solution `x + y√D` to its principal ideal and
extends it to a divisor of `(M)` in the maximal quadratic order.  The
number of such maximal-order ideal divisors is proved below in Lean, using
unique factorization of ideals and quadratic splitting.  The historical
source-shaped interface records a conductor comparison through at most three
unit cosets.  The production route instead discharges the `Fin 4` interface
internally: it colours relative units by the four residue classes of
`O_K / 2 O_K` and proves that equality of colours descends to equality of
principal ideals in `Zsqrtd`.
-/

structure QuadraticOrderConductorData (D : ℕ) (M : ℤ) where
  K : Type
  [fieldK : Field K]
  [numberFieldK : NumberField K]
  [quadraticK : Algebra.IsQuadraticExtension ℚ K]
  idealOf :
    ℤ × ℤ →
      {I : Ideal (𝓞 K) //
        I ∣ Ideal.span ({(M : 𝓞 K)} : Set (𝓞 K))}
  conductorColour : ℤ × ℤ → Fin 4
  same_principalIdeal_of_same_extension :
    ∀ s t : ℤ × ℤ,
      s.1 ^ 2 - (D : ℤ) * s.2 ^ 2 = M →
      t.1 ^ 2 - (D : ℤ) * t.2 ^ 2 = M →
      conductorColour s = conductorColour t →
      idealOf s = idealOf t →
      Ideal.span
          ({toZsqrtd D s} : Set (ℤ√(D : ℤ))) =
        Ideal.span
          ({toZsqrtd D t} : Set (ℤ√(D : ℤ)))


def QuadraticOrderConductorFiberBoundStatement : Prop :=
  ∀ (D : ℕ) (M : ℤ),
    0 < D →
    Squarefree D →
    ¬ IsSquare (D : ℚ) →
    M ≠ 0 →
    Nonempty (QuadraticOrderConductorData D M)

/--
Multiplication by a norm-one Pell solution, written on integral
coordinates.
-/
def act
    {D : ℕ} (u : Pell.Solution₁ (D : ℤ))
    (s : ℤ × ℤ) : ℤ × ℤ :=
  (u.x * s.1 + (D : ℤ) * (u.y * s.2),
    u.x * s.2 + u.y * s.1)

@[simp]
theorem toZsqrtd_act
    {D : ℕ} (u : Pell.Solution₁ (D : ℤ))
    (s : ℤ × ℤ) :
    toZsqrtd D (act u s) =
      (u : ℤ√(D : ℤ)) * toZsqrtd D s := by
  ext <;> simp only [act, toZsqrtd, Zsqrtd.re_mul, Zsqrtd.im_mul]
  · change
      u.x * s.1 + (D : ℤ) * (u.y * s.2) =
        u.x * s.1 + (D : ℤ) * u.y * s.2
    ring
  · change u.x * s.2 + u.y * s.1 =
      u.x * s.2 + u.y * s.1
    rfl

/-- A Pell unit preserves every nonzero or zero norm fibre. -/
theorem act_preserves_equation
    {D : ℕ} {M : ℤ}
    (u : Pell.Solution₁ (D : ℤ))
    {s : ℤ × ℤ}
    (hs : s.1 ^ 2 - (D : ℤ) * s.2 ^ 2 = M) :
    (act u s).1 ^ 2 -
        (D : ℤ) * (act u s).2 ^ 2 = M := by
  have huNorm : (u : ℤ√(D : ℤ)).norm = 1 := by
    rw [Zsqrtd.norm_def]
    change u.x * u.x - (D : ℤ) * u.y * u.y = 1
    simpa only [pow_two, mul_assoc] using u.prop
  rw [generalizedPellEquation_iff_norm,
    toZsqrtd_act, Zsqrtd.norm_mul, huNorm,
    generalizedPellEquation_iff_norm.mp hs, one_mul]

/-- The coordinate action is invertible; hence it is injective. -/
theorem act_inv
    {D : ℕ} (u : Pell.Solution₁ (D : ℤ))
    (s : ℤ × ℤ) :
    act u⁻¹ (act u s) = s := by
  have h :
      toZsqrtd D (act u⁻¹ (act u s)) =
        toZsqrtd D s := by
    rw [toZsqrtd_act, toZsqrtd_act, ← mul_assoc]
    have hu :
        (u⁻¹ : Pell.Solution₁ (D : ℤ)) * u = 1 := by
      simp
    have hu' :
        ((u⁻¹ : Pell.Solution₁ (D : ℤ)) :
            ℤ√(D : ℤ)) * (u : ℤ√(D : ℤ)) = 1 := by
      exact congrArg
        (fun v : Pell.Solution₁ (D : ℤ) ↦
          (v : ℤ√(D : ℤ))) hu
    rw [hu', one_mul]
  exact Prod.ext (congrArg Zsqrtd.re h) (congrArg Zsqrtd.im h)

theorem act_injective
    {D : ℕ} (u : Pell.Solution₁ (D : ℤ)) :
    Function.Injective (act u) := by
  intro s t h
  have := congrArg (act u⁻¹) h
  simpa only [act_inv] using this

/--
The principal ideal generated by a norm-`M` element divides the principal
ideal `(M)`.  This is the exact algebraic map used in the manuscript before
unique factorisation of ideals is invoked.
-/
theorem principalIdeal_dvd_intCast
    {D : ℕ} {M : ℤ} {s : ℤ × ℤ}
    (hs : s.1 ^ 2 - (D : ℤ) * s.2 ^ 2 = M) :
    Ideal.span ({toZsqrtd D s} : Set (ℤ√(D : ℤ))) ∣
      Ideal.span ({(M : ℤ√(D : ℤ))} : Set (ℤ√(D : ℤ))) := by
  refine ⟨Ideal.span ({star (toZsqrtd D s)} :
      Set (ℤ√(D : ℤ))), ?_⟩
  rw [Ideal.span_singleton_mul_span_singleton,
    ← Zsqrtd.norm_eq_mul_conj,
    generalizedPellEquation_iff_norm.mp hs]

/--
Equality of two principal ideals in one nonzero norm fibre gives a
norm-one `Zsqrtd` unit, hence a genuine `Pell.Solution₁`.

This is the rigorous unit-orbit statement available without constructing a
quadratic number field.  The `Nonsquare` instance is supplied from the
rational nonsquare hypothesis used by `PellInput`.
-/
theorem same_principalIdeal_gives_pell_unit
    {D : ℕ} {M : ℤ} (hD : ¬ IsSquare (D : ℚ))
    (hM : M ≠ 0) {s t : ℤ × ℤ}
    (hs : s.1 ^ 2 - (D : ℤ) * s.2 ^ 2 = M)
    (ht : t.1 ^ 2 - (D : ℤ) * t.2 ^ 2 = M)
    (hideal :
      Ideal.span ({toZsqrtd D s} : Set (ℤ√(D : ℤ))) =
        Ideal.span ({toZsqrtd D t} : Set (ℤ√(D : ℤ)))) :
    ∃ u : Pell.Solution₁ (D : ℤ),
      toZsqrtd D s * (u : ℤ√(D : ℤ)) = toZsqrtd D t := by
  let : Zsqrtd.Nonsquare D :=
    ⟨fun n hn ↦ hD ⟨(n : ℚ), by
      exact_mod_cast hn⟩⟩
  have hassociated :
      Associated (toZsqrtd D s) (toZsqrtd D t) :=
    Ideal.span_singleton_eq_span_singleton.mp hideal
  obtain ⟨u, hu⟩ := hassociated
  have hnormu : (u : ℤ√(D : ℤ)).norm = 1 := by
    have hnormeq := congrArg Zsqrtd.norm hu
    rw [Zsqrtd.norm_mul,
      generalizedPellEquation_iff_norm.mp hs,
      generalizedPellEquation_iff_norm.mp ht] at hnormeq
    apply mul_left_cancel₀ hM
    simpa only [mul_one] using hnormeq
  let pu : Pell.Solution₁ (D : ℤ) :=
    ⟨(u : ℤ√(D : ℤ)),
      Pell.is_pell_solution_iff_mem_unitary.mp (by
        simpa only [Zsqrtd.norm_def, pow_two, mul_assoc] using hnormu)⟩
  exact ⟨pu, by simpa only [pu] using hu⟩

/--
If two height-`H` solutions lie in the same principal-ideal fibre, the
`y`-coordinate of the quotient Pell unit is at most `2H²`.

This estimate avoids embeddings: from `t = s*u` and
`s * star(s) = M`, one gets
`M*u.y = s.x*t.y - s.y*t.x`.
-/
theorem pellUnit_y_natAbs_le
    {D H : ℕ} {M : ℤ} (hM : M ≠ 0)
    {s t : ℤ × ℤ} (u : Pell.Solution₁ (D : ℤ))
    (hsEq : s.1 ^ 2 - (D : ℤ) * s.2 ^ 2 = M)
    (hu :
      toZsqrtd D s * (u : ℤ√(D : ℤ)) =
        toZsqrtd D t)
    (hsx : s.1.natAbs ≤ H) (hsy : s.2.natAbs ≤ H)
    (htx : t.1.natAbs ≤ H) (hty : t.2.natAbs ≤ H) :
    u.y.natAbs ≤ 2 * H ^ 2 := by
  have hprod :
      star (toZsqrtd D s) * toZsqrtd D t =
        (M : ℤ√(D : ℤ)) * (u : ℤ√(D : ℤ)) := by
    calc
      star (toZsqrtd D s) * toZsqrtd D t =
          star (toZsqrtd D s) *
            (toZsqrtd D s * (u : ℤ√(D : ℤ))) := by rw [hu]
      _ = (toZsqrtd D s * star (toZsqrtd D s)) *
          (u : ℤ√(D : ℤ)) := by ring
      _ = ((toZsqrtd D s).norm : ℤ√(D : ℤ)) *
          (u : ℤ√(D : ℤ)) := by
        rw [Zsqrtd.norm_eq_mul_conj]
      _ = (M : ℤ√(D : ℤ)) * (u : ℤ√(D : ℤ)) := by
        rw [generalizedPellEquation_iff_norm.mp hsEq]
  have hcrossRaw := congrArg Zsqrtd.im hprod
  have hcross :
      M * u.y = s.1 * t.2 - s.2 * t.1 := by
    simpa only [Zsqrtd.im_mul, Zsqrtd.re_star, Zsqrtd.im_star,
      toZsqrtd_re, toZsqrtd_im, Zsqrtd.re_intCast,
      Zsqrtd.im_intCast, Pell.Solution₁.y, sub_eq_add_neg,
      neg_mul, zero_mul, add_zero] using hcrossRaw.symm
  calc
    u.y.natAbs ≤ M.natAbs * u.y.natAbs :=
      Nat.le_mul_of_pos_left _ (Int.natAbs_pos.mpr hM)
    _ = (M * u.y).natAbs := by rw [Int.natAbs_mul]
    _ = (s.1 * t.2 - s.2 * t.1).natAbs := by rw [hcross]
    _ ≤ (s.1 * t.2).natAbs + (s.2 * t.1).natAbs :=
      Int.natAbs_sub_le _ _
    _ = s.1.natAbs * t.2.natAbs +
        s.2.natAbs * t.1.natAbs := by
      rw [Int.natAbs_mul, Int.natAbs_mul]
    _ ≤ H * H + H * H :=
      Nat.add_le_add (Nat.mul_le_mul hsx hty)
        (Nat.mul_le_mul hsy htx)
    _ = 2 * H ^ 2 := by ring

/-! ## Quantitative size of one Pell-unit orbit -/

/--
The `y`-coordinate of successive positive powers of a fundamental Pell
solution grows at least geometrically with ratio `2`.
-/
theorem two_pow_le_y_pow_succ
    {d : ℤ} {ε : Pell.Solution₁ d}
    (hε : Pell.IsFundamental ε) :
    ∀ n : ℕ, (2 : ℤ) ^ n ≤ (ε ^ (n + 1)).y := by
  intro n
  induction n with
  | zero =>
      have hy : 0 < ε.y := hε.2.1
      simp only [pow_zero, zero_add, pow_one]
      omega
  | succ n ih =>
      have hxpow :
          0 < (ε ^ (n + 1)).x :=
        Pell.Solution₁.x_pow_pos hε.x_pos _
      have hypow :
          0 ≤ (ε ^ (n + 1)).y :=
        le_trans (by positivity : (0 : ℤ) ≤ 2 ^ n) ih
      have hεxStrict : (1 : ℤ) < ε.x := hε.1
      have hεx : (2 : ℤ) ≤ ε.x := by omega
      have hfirst :
          0 ≤ (ε ^ (n + 1)).x * ε.y :=
        mul_nonneg hxpow.le hε.2.1.le
      calc
        (2 : ℤ) ^ (n + 1) = 2 * (2 : ℤ) ^ n := by
          rw [pow_succ']
        _ ≤ 2 * (ε ^ (n + 1)).y :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ ≤ (ε ^ (n + 1)).y * ε.x :=
          by
            simpa only [mul_comm] using
              mul_le_mul_of_nonneg_right hεx hypow
        _ ≤ (ε ^ (n + 1)).x * ε.y +
            (ε ^ (n + 1)).y * ε.x :=
          le_add_of_nonneg_left hfirst
        _ = (ε ^ ((n + 1) + 1)).y := by
          calc
            _ = ((ε ^ (n + 1)) * ε).y :=
              (Pell.Solution₁.y_mul _ _).symm
            _ = (ε ^ ((n + 1) + 1)).y :=
              congrArg Pell.Solution₁.y
                (pow_succ ε (n + 1)).symm

theorem two_pow_le_y_natAbs_pow_succ
    {d : ℤ} {ε : Pell.Solution₁ d}
    (hε : Pell.IsFundamental ε) (n : ℕ) :
    2 ^ n ≤ (ε ^ (n + 1)).y.natAbs := by
  have hy :
      0 < (ε ^ (n + 1)).y :=
    Pell.Solution₁.y_pow_succ_pos hε.x_pos hε.2.1 n
  rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs,
    abs_of_nonneg hy.le]
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    two_pow_le_y_pow_succ hε n

/--
For a nonzero exponent, the exponent size is controlled by the
`y`-coordinate of the corresponding Pell unit.
-/
theorem two_pow_pred_natAbs_le_y_natAbs_zpow
    {d : ℤ} {ε : Pell.Solution₁ d}
    (hε : Pell.IsFundamental ε) (n : ℤ) (hn : n ≠ 0) :
    2 ^ (n.natAbs - 1) ≤ (ε ^ n).y.natAbs := by
  cases n with
  | ofNat k =>
      cases k with
      | zero => exact (hn rfl).elim
      | succ k =>
          simpa only [Int.natAbs_natCast, Nat.succ_sub_one,
            Int.ofNat_eq_natCast, zpow_natCast] using
            two_pow_le_y_natAbs_pow_succ hε k
  | negSucc k =>
      simpa only [Int.natAbs_negSucc, Nat.succ_sub_one,
        zpow_negSucc, Pell.Solution₁.y_inv, Int.natAbs_neg] using
        two_pow_le_y_natAbs_pow_succ hε k

/--
Any exponent producing a Pell unit with `|y| ≤ Y` lies in the symmetric
integer interval of radius `log₂(Y)+1`.
-/
theorem natAbs_exponent_le_log_add_one
    {d : ℤ} {ε : Pell.Solution₁ d}
    (hε : Pell.IsFundamental ε) {n : ℤ} {Y : ℕ}
    (hy : (ε ^ n).y.natAbs ≤ Y) :
    n.natAbs ≤ Nat.log 2 Y + 1 := by
  by_cases hn : n = 0
  · subst n
    simp
  have hpow :
      2 ^ (n.natAbs - 1) ≤ Y :=
    (two_pow_pred_natAbs_le_y_natAbs_zpow hε n hn).trans hy
  have hY : Y ≠ 0 := by
    intro hY
    subst Y
    have hpos : 0 < 2 ^ (n.natAbs - 1) := by positivity
    omega
  have hlog :
      n.natAbs - 1 ≤ Nat.log 2 Y :=
    Nat.le_log_of_pow_le (by norm_num) hpow
  have hnabs : 0 < n.natAbs :=
    Int.natAbs_pos.mpr hn
  omega

/--
Explicit logarithmic count for the norm-one Pell units whose
`y`-coordinate lies in a symmetric box.

The harmless factor `2` records the alternatives `ε^n` and `-ε^n`.
-/
theorem card_pellUnits_y_natAbs_le
    {d : ℤ} {ε : Pell.Solution₁ d}
    (hε : Pell.IsFundamental ε)
    (Y : ℕ) (s : Finset (Pell.Solution₁ d))
    (hs : ∀ u ∈ s, u.y.natAbs ≤ Y) :
    s.card ≤ 2 * (2 * (Nat.log 2 Y + 1) + 1) := by
  classical
  let L : ℕ := Nat.log 2 Y + 1
  let exps : Finset ℤ :=
    Finset.Icc (-(L : ℤ)) (L : ℤ)
  let powers : Finset (Pell.Solution₁ d) :=
    exps.image (fun n : ℤ ↦ ε ^ n)
  let negPowers : Finset (Pell.Solution₁ d) :=
    exps.image (fun n : ℤ ↦ -ε ^ n)
  have hsubset : s ⊆ powers ∪ negPowers := by
    intro u hu
    obtain ⟨n, hn | hn⟩ := hε.eq_zpow_or_neg_zpow u
    · have hnBound :
          n.natAbs ≤ L := by
        apply natAbs_exponent_le_log_add_one hε
        simpa only [hn] using hs u hu
      have hnIcc : n ∈ exps := by
        simp only [exps, Finset.mem_Icc]
        have hcast :
            (n.natAbs : ℤ) ≤ (L : ℤ) := by
          exact_mod_cast hnBound
        have habs : |n| ≤ (L : ℤ) := by
          simpa only [Int.natCast_natAbs] using hcast
        exact abs_le.mp habs
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨n, hnIcc, hn.symm⟩)
    · have hnBound :
          n.natAbs ≤ L := by
        apply natAbs_exponent_le_log_add_one hε
        have hy := hs u hu
        rw [hn, Pell.Solution₁.y_neg, Int.natAbs_neg] at hy
        exact hy
      have hnIcc : n ∈ exps := by
        simp only [exps, Finset.mem_Icc]
        have hcast :
            (n.natAbs : ℤ) ≤ (L : ℤ) := by
          exact_mod_cast hnBound
        have habs : |n| ≤ (L : ℤ) := by
          simpa only [Int.natCast_natAbs] using hcast
        exact abs_le.mp habs
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨n, hnIcc, hn.symm⟩)
  calc
    s.card ≤ (powers ∪ negPowers).card :=
      Finset.card_le_card hsubset
    _ ≤ powers.card + negPowers.card :=
      Finset.card_union_le _ _
    _ ≤ exps.card + exps.card :=
      Nat.add_le_add
        (show powers.card ≤ exps.card by
          dsimp only [powers]
          exact Finset.card_image_le)
        (show negPowers.card ≤ exps.card by
          dsimp only [negPowers]
          exact Finset.card_image_le)
    _ = 2 * (2 * L + 1) := by
      have hexps : exps.card = 2 * L + 1 := by
        simp only [exps, Int.card_Icc]
        have hnonneg :
            (0 : ℤ) ≤ (L : ℤ) + 1 - (-(L : ℤ)) := by
          omega
        rw [← Int.ofNat_inj,
          Int.toNat_of_nonneg hnonneg]
        push_cast
        ring
      rw [hexps]
      ring
    _ = 2 * (2 * (Nat.log 2 Y + 1) + 1) := rfl

/-- The explicit logarithmic number of unit translates in a height-`H` box. -/
def pellUnitOrbitEnvelope (H : ℕ) : ℕ :=
  2 * (2 * (Nat.log 2 (2 * H ^ 2) + 1) + 1)

/--
Complete quantitative bound for one principal-ideal fibre of generalized
Pell solutions in a height box.

This is the orbit-counting half of Lemma 9.2.  What remains for the full
lemma is to bound the number of distinct principal ideals that can occur.
-/
theorem card_samePrincipalIdeal_solutionFiber
    {D H : ℕ} {M : ℤ}
    (hD : ¬ IsSquare (D : ℚ)) (hM : M ≠ 0)
    (base : ℤ × ℤ)
    (hbase :
      PellInput.generalizedPellBox D M H base)
    (s : Finset (ℤ × ℤ))
    (hs :
      ∀ t ∈ s, PellInput.generalizedPellBox D M H t)
    (hideal :
      ∀ t ∈ s,
        Ideal.span ({toZsqrtd D base} : Set (ℤ√(D : ℤ))) =
          Ideal.span ({toZsqrtd D t} : Set (ℤ√(D : ℤ)))) :
    s.card ≤
      pellUnitOrbitEnvelope H := by
  classical
  obtain ⟨ε, hε⟩ :=
    Pell.IsFundamental.exists_of_not_isSquare
      (show (0 : ℤ) < D by
        have hDpos : 0 < D := by
          by_contra h
          have hDzero : D = 0 := Nat.eq_zero_of_not_pos h
          subst D
          exact hD ⟨0, by norm_num⟩
        exact_mod_cast hDpos)
      (fun hDsquare ↦
        hD (by
          obtain ⟨z, hz⟩ := hDsquare
          exact ⟨(z : ℚ), by exact_mod_cast hz⟩))
  let f : {t : ℤ × ℤ // t ∈ s} →
      Pell.Solution₁ (D : ℤ) :=
    fun t ↦ Classical.choose
      (same_principalIdeal_gives_pell_unit hD hM
        hbase.1 (hs t t.property).1
        (hideal t t.property))
  have hf_spec :
      ∀ t : {t : ℤ × ℤ // t ∈ s},
        toZsqrtd D base *
            (f t : ℤ√(D : ℤ)) =
          toZsqrtd D t := by
    intro t
    simpa only [f] using
      Classical.choose_spec
        (same_principalIdeal_gives_pell_unit hD hM
          hbase.1 (hs t t.property).1
          (hideal t t.property))
  have hf_injective : Function.Injective f := by
    intro t₁ t₂ h
    apply Subtype.ext
    have ht :
        toZsqrtd D (t₁ : ℤ × ℤ) =
          toZsqrtd D (t₂ : ℤ × ℤ) := by
      rw [← hf_spec t₁, ← hf_spec t₂, h]
    exact Prod.ext (congrArg Zsqrtd.re ht)
      (congrArg Zsqrtd.im ht)
  let units : Finset (Pell.Solution₁ (D : ℤ)) :=
    s.attach.image f
  have hunits :
      ∀ u ∈ units, u.y.natAbs ≤ 2 * H ^ 2 := by
    intro u hu
    obtain ⟨t, _ht, rfl⟩ := Finset.mem_image.mp hu
    exact pellUnit_y_natAbs_le hM (f t) hbase.1 (hf_spec t)
      hbase.2.1 hbase.2.2
      (hs t t.property).2.1 (hs t t.property).2.2
  have hcard :=
    card_pellUnits_y_natAbs_le hε (2 * H ^ 2) units hunits
  simpa only [units, Finset.card_image_of_injective _ hf_injective,
    Finset.card_attach, pellUnitOrbitEnvelope] using hcard

/--
For squarefree `D`, combine the conductor comparison, the Lean proof that
`(M)` has at most `τ(|M|)²` maximal-order ideal divisors, and the formalized
unit-orbit estimate.
-/
theorem squarefreeGeneralizedPellBox_atMost_of_conductorComparison
    (hConductor : QuadraticOrderConductorFiberBoundStatement)
    {D H : ℕ} {M : ℤ}
    (hDpos : 0 < D) (hDsquarefree : Squarefree D)
    (hD : ¬ IsSquare (D : ℚ)) (hM : M ≠ 0) :
    PellInput.HasAtMostSolutionsReal
      (PellInput.generalizedPellBox D M H)
      (((4 * M.natAbs.divisors.card ^ 2) *
          pellUnitOrbitEnvelope H : ℕ) : ℝ) := by
  classical
  obtain ⟨data⟩ :=
    hConductor D M hDpos hDsquarefree hD hM
  let : Field data.K := data.fieldK
  let : NumberField data.K := data.numberFieldK
  let : Algebra.IsQuadraticExtension ℚ data.K :=
    data.quadraticK
  let IdealDivisor :=
    {I : Ideal (𝓞 data.K) //
      I ∣ Ideal.span ({(M : 𝓞 data.K)} : Set (𝓞 data.K))}
  let : Fintype IdealDivisor :=
    UniqueFactorizationMonoid.fintypeSubtypeDvd
      (Ideal.span ({(M : 𝓞 data.K)} : Set (𝓞 data.K)))
      (by
        rw [Ideal.zero_eq_bot]
        exact mt Ideal.span_singleton_eq_bot.mp
          (Int.cast_ne_zero.mpr hM))
  let Colour := Fin 4 × IdealDivisor
  let classOf : ℤ × ℤ → Colour :=
    fun t ↦ (data.conductorColour t, data.idealOf t)
  intro s hs
  let E : ℕ := pellUnitOrbitEnvelope H
  have hfibre :
      ∀ i : Colour,
        (s.filter fun t ↦ classOf t = i).card ≤ E := by
    intro i
    by_cases hi : (s.filter fun t ↦ classOf t = i).Nonempty
    · obtain ⟨base, hbase⟩ := hi
      have hbaseMem : base ∈ s :=
        (Finset.mem_filter.mp hbase).1
      have hbaseClass : classOf base = i :=
        (Finset.mem_filter.mp hbase).2
      apply card_samePrincipalIdeal_solutionFiber
        hD hM base (hs base hbaseMem)
      · intro t ht
        exact hs t (Finset.mem_filter.mp ht).1
      · intro t ht
        have htClass : classOf t = i :=
          (Finset.mem_filter.mp ht).2
        have hsameClass : classOf base = classOf t :=
          hbaseClass.trans htClass.symm
        have hsameConductor :
            data.conductorColour base =
              data.conductorColour t := by
          simpa only [classOf] using congrArg Prod.fst hsameClass
        have hsameIdeal :
            data.idealOf base = data.idealOf t := by
          simpa only [classOf] using congrArg Prod.snd hsameClass
        exact data.same_principalIdeal_of_same_extension base t
          (hs base hbaseMem).1
          (hs t (Finset.mem_filter.mp ht).1).1
          hsameConductor hsameIdeal
    · rw [Finset.not_nonempty_iff_eq_empty.mp hi]
      simp [E]
  have hpartition :
      s.card =
        ∑ i : Colour, (s.filter fun t ↦ classOf t = i).card := by
    simpa using
      (Finset.card_eq_sum_card_fiberwise
        (s := s) (t := Finset.univ) (f := classOf)
        (by intro x hx; simp))
  have hcard : s.card ≤ Fintype.card Colour * E := by
    calc
      s.card =
          ∑ i : Colour,
            (s.filter fun t ↦ classOf t = i).card :=
        hpartition
      _ ≤ ∑ _i : Colour, E :=
        Finset.sum_le_sum fun i _hi ↦ hfibre i
      _ = Fintype.card Colour * E := by simp
  have hIdealCount :
      Fintype.card IdealDivisor ≤
        M.natAbs.divisors.card ^ 2 := by
    simpa only [Nat.card_eq_fintype_card] using
      (QuadraticIdealDivisors.quadraticIdealDivisorTauSq
        data.K M hM)
  have hColourCount :
      Fintype.card Colour ≤
        4 * M.natAbs.divisors.card ^ 2 := by
    simpa only [Colour, Fintype.card_prod, Fintype.card_fin] using
      Nat.mul_le_mul_left 4 hIdealCount
  have htotal :
      s.card ≤
        (4 * M.natAbs.divisors.card ^ 2) * E :=
    hcard.trans (Nat.mul_le_mul_right E hColourCount)
  exact_mod_cast htotal

/-! ## Reduction to the squarefree kernel -/

/-- Replace `y` with `b*y` when `D = b²*a`. -/
def scaleImag (b : ℕ) (s : ℤ × ℤ) : ℤ × ℤ :=
  (s.1, (b : ℤ) * s.2)

theorem scaleImag_preserves_equation
    {D a b : ℕ} {M : ℤ} {s : ℤ × ℤ}
    (hD : b ^ 2 * a = D)
    (hs : s.1 ^ 2 - (D : ℤ) * s.2 ^ 2 = M) :
    (scaleImag b s).1 ^ 2 -
        (a : ℤ) * (scaleImag b s).2 ^ 2 = M := by
  dsimp only [scaleImag]
  have hD' : (b : ℤ) ^ 2 * (a : ℤ) = (D : ℤ) := by
    exact_mod_cast hD
  rw [← hs]
  rw [← hD']
  ring

theorem scaleImag_injective
    {b : ℕ} (hb : 0 < b) :
    Function.Injective (scaleImag b) := by
  intro s t h
  have hfirst := congrArg Prod.fst h
  have hsecond := congrArg Prod.snd h
  dsimp only [scaleImag] at hfirst hsecond
  have hb0 : (b : ℤ) ≠ 0 := by exact_mod_cast hb.ne'
  exact Prod.ext hfirst (mul_left_cancel₀ hb0 hsecond)

theorem scaleImag_height
    {b H : ℕ} {s : ℤ × ℤ}
    (hy : s.2.natAbs ≤ H) :
    (scaleImag b s).2.natAbs ≤ b * H := by
  dsimp only [scaleImag]
  rw [Int.natAbs_mul, Int.natAbs_natCast]
  exact Nat.mul_le_mul_left b hy

/--
Every positive nonsquare `D` admits a squarefree decomposition
`D = b²*a`, and the squarefree factor remains nonsquare over `ℚ`.

`Nat.sq_mul_squarefree_of_pos` is the only Mathlib lemma needed for the
existence of this reduction.
-/
theorem exists_squarefree_reduction
    {D : ℕ} (hDpos : 0 < D)
    (hD : ¬ IsSquare (D : ℚ)) :
    ∃ a b : ℕ,
      0 < a ∧ 0 < b ∧ Squarefree a ∧
      b ^ 2 * a = D ∧ ¬ IsSquare (a : ℚ) := by
  obtain ⟨a, b, ha, hb, hab, haSquarefree⟩ :=
    Nat.sq_mul_squarefree_of_pos hDpos
  refine ⟨a, b, ha, hb, haSquarefree, hab, ?_⟩
  rintro ⟨q, hq⟩
  apply hD
  refine ⟨(b : ℚ) * q, ?_⟩
  calc
    (D : ℚ) = ((b ^ 2 * a : ℕ) : ℚ) := by rw [hab]
    _ = (b : ℚ) ^ 2 * (a : ℚ) := by norm_num
    _ = (b : ℚ) ^ 2 * (q * q) := by rw [hq]
    _ = ((b : ℚ) * q) * ((b : ℚ) * q) := by ring

/--
The squarefree-kernel substitution transfers the finite counting statement
without loss.  The target height `D*H` is deliberately coarse; in the
polynomial regime it only doubles the exponent.
-/
theorem hasAtMostSolutionsReal_of_squarefree_reduction
    {D a b H : ℕ} {M : ℤ} {B : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hdecomp : b ^ 2 * a = D)
    (hcount :
      PellInput.HasAtMostSolutionsReal
        (PellInput.generalizedPellBox a M (D * H)) B) :
    PellInput.HasAtMostSolutionsReal
      (PellInput.generalizedPellBox D M H) B := by
  have hDpos : 0 < D := by
    rw [← hdecomp]
    positivity
  have hbD : b ≤ D := by
    calc
      b ≤ b ^ 2 := by nlinarith
      _ ≤ b ^ 2 * a := Nat.le_mul_of_pos_right _ ha
      _ = D := hdecomp
  intro s hs
  let f : ℤ × ℤ → ℤ × ℤ := scaleImag b
  have hf : Function.Injective f := by
    simpa only [f] using scaleImag_injective hb
  have himage :
      ∀ t ∈ s.image f,
        PellInput.generalizedPellBox a M (D * H) t := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨heq, hx, hy⟩ := hs u hu
    refine ⟨scaleImag_preserves_equation hdecomp heq,
      hx.trans (Nat.le_mul_of_pos_left H hDpos), ?_⟩
    exact (scaleImag_height hy).trans
      (Nat.mul_le_mul_right H hbD)
  have hcard := hcount (s.image f) himage
  simpa only [Finset.card_image_of_injective _ hf] using hcard


end PaperP1.PellInput

