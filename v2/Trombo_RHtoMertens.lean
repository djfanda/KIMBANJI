import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Trombo hypothesis ladder: toward `RH → MertensBound` (PARTIAL)

The classical converse `RH → MertensBound` (Littlewood 1912; Titchmarsh §14.25) goes:
1. under RH, `(s - 1) ζ(s)` has a holomorphic logarithm on `re s > 1/2` (`log ζ` itself has no single-valued branch on `{re s > 1/2} \ {1}`, because of the pole);
2. Borel–Carathéodory / Hadamard three circles applied to `log ζ` give
   `1/ζ(σ + it) = O(|t|^ε)` for `σ ≥ 1/2 + δ`;
3. a truncated Perron formula for `M(x) = ∑_{n ≤ x} μ(n)` with `1/ζ`, moved to `re s = 1/2 + ε`.

This file proves ONLY step 1, in the following exact form (the pole at `s = 1` is removed by
`Z s := (s - 1) ζ(s)`, `Z 1 := 1`):

* `RH_iff_exists_log` : `RiemannHypothesis ↔ ∃ L : ℂ → ℂ, DifferentiableOn ℂ L {s | 1/2 < re s} ∧
   ∀ s, 1/2 < re s → exp (L s) = Z s`.

Steps 2 and 3 are NOT proved. Mathlib (this snapshot) has no Perron formula, and only
lemma-level pieces of Borel–Carathéodory. Hence, in Trombo, `MertensBound ⇔ RH` remains
ONE-DIRECTIONAL: only `MertensBound → RH` is proved (`Trombo_Mertens.lean`, `Trombo_RHEquiv.lean`).
-/

open Complex Filter Set Topology

namespace TromboRHtoMertens

/-- Unconditional: a zero `s ≠ 1` of `ζ` that is not of the form `-2(n+1)` lies in the open
critical strip `0 < re s < 1`. (Same proof as in `Trombo_GRH.lean`.) -/
lemma zeta_zero_in_strip {s : ℂ} (hz : riemannZeta s = 0)
    (htriv : ¬∃ n : ℕ, s = -2 * (n + 1)) : 0 < s.re ∧ s.re < 1 := by
  constructor
  · by_contra hle
    push Not at hle
    have hs0 : s ≠ 0 := by
      rintro rfl; rw [riemannZeta_zero] at hz; norm_num at hz
    set w : ℂ := 1 - s with hw
    have hwre : 1 ≤ w.re := by simp [hw]; linarith
    have hwn : ∀ n : ℕ, w ≠ -n := by
      intro n h
      have : w.re = -(n : ℝ) := by rw [h]; simp
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hw1 : w ≠ 1 := by
      intro h; apply hs0; rw [hw] at h; linear_combination -h
    have hfe := riemannZeta_one_sub hwn hw1
    have h1w : 1 - w = s := by rw [hw]; ring
    rw [h1w, hz] at hfe
    have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
    have hA : (2 : ℂ) * (2 * Real.pi) ^ (-w) ≠ 0 := by
      refine mul_ne_zero two_ne_zero ?_
      rw [cpow_def_of_ne_zero (mul_ne_zero two_ne_zero hpi)]
      exact exp_ne_zero _
    have hG : Gamma w ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
    have hZ : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re hwre
    have hcos : cos (Real.pi * w / 2) = 0 := by
      by_contra hc
      exact (mul_ne_zero (mul_ne_zero (mul_ne_zero hA hG) hc) hZ) hfe.symm
    obtain ⟨k, hk⟩ := cos_eq_zero_iff.1 hcos
    have hwk : w = 2 * k + 1 := by
      have : Real.pi * w = Real.pi * (2 * k + 1) := by linear_combination 2 * hk
      exact mul_left_cancel₀ hpi this
    have hsk : s = -2 * (k : ℂ) := by linear_combination -hwk - hw
    have hkre : s.re = -2 * (k : ℝ) := by rw [hsk]; simp
    have hk0 : 0 ≤ k := by
      have : (0 : ℝ) ≤ k := by linarith
      exact_mod_cast this
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk0
    rcases Nat.eq_zero_or_pos m with hm | hm
    · apply hs0; rw [hsk, hm]; simp
    · apply htriv
      refine ⟨m - 1, ?_⟩
      rw [hsk]
      have : ((m - 1 : ℕ) : ℂ) + 1 = (m : ℂ) := by
        rw [Nat.cast_sub hm]; push_cast; ring
      rw [this]; push_cast; ring
  · by_contra hge
    push Not at hge
    exact riemannZeta_ne_zero_of_one_le_re hge hz

/-- Unconditional: a point with positive real part is not a trivial zero `-2(n+1)`. -/
lemma not_trivial_of_re_pos {s : ℂ} (hs : 0 < s.re) : ¬∃ n : ℕ, s = -2 * (n + 1) := by
  rintro ⟨n, rfl⟩
  have : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
  rw [this] at hs
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- Unconditional reflection: if `ζ s = 0`, `0 < re s` and `s ≠ 1`, then `ζ (1 - s) = 0`. -/
lemma zeta_one_sub_eq_zero {s : ℂ} (hz : riemannZeta s = 0) (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta (1 - s) = 0 := by
  have hn : ∀ n : ℕ, s ≠ -n := by
    intro n h
    have : s.re = -(n : ℝ) := by rw [h]; simp
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hfe := riemannZeta_one_sub hn hs1
  rw [hz, mul_zero] at hfe
  exact hfe

/-- **RH, half-plane form.** Mathlib's `RiemannHypothesis` holds iff `ζ s ≠ 0` for every `s`
with `1/2 < re s`. The point `s = 1` is included on the right; there `ζ 1` is Mathlib's junk value,
which is nonzero (`riemannZeta_one_ne_zero`). -/
theorem RH_iff_noZerosRightHalf :
    RiemannHypothesis ↔ ∀ s : ℂ, 1 / 2 < s.re → riemannZeta s ≠ 0 := by
  constructor
  · intro hRH s hs hz
    by_cases hs1 : s = 1
    · subst hs1; exact riemannZeta_one_ne_zero hz
    · have h := hRH s hz (not_trivial_of_re_pos (by linarith)) hs1
      linarith
  · intro h s hz htriv hs1
    obtain ⟨h0, h1⟩ := zeta_zero_in_strip hz htriv
    rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
    · exfalso
      exact h (1 - s) (by simp; linarith) (zeta_one_sub_eq_zero hz h0 hs1)
    · exact heq
    · exact absurd hz (h s hgt)


/-! ## Removing the pole: `Z s = (s - 1) ζ(s)`, `Z 1 = 1` -/

/-- `Z s = (s - 1) ζ(s)` for `s ≠ 1`, and `Z 1 = 1` (the residue of `ζ` at `1`). -/
noncomputable def Z : ℂ → ℂ := Function.update (fun s => (s - 1) * riemannZeta s) 1 1

lemma Z_of_ne {s : ℂ} (hs : s ≠ 1) : Z s = (s - 1) * riemannZeta s := by
  simp [Z, Function.update_of_ne hs]

lemma Z_one : Z 1 = 1 := by simp [Z]

/-- `Z` is differentiable at every `s ≠ 1`. -/
lemma Z_differentiableAt_of_ne {s : ℂ} (hs : s ≠ 1) : DifferentiableAt ℂ Z s := by
  have hd : DifferentiableAt ℂ (fun s => (s - 1) * riemannZeta s) s :=
    (differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hs)
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_compl_singleton.mem_nhds hs] with z hz
  exact Z_of_ne hz

/-- Unconditional: `Z` is entire (removable singularity at `s = 1`). -/
lemma Z_differentiable : Differentiable ℂ Z := by
  intro s
  rcases ne_or_eq s 1 with hs | rfl
  · exact Z_differentiableAt_of_ne hs
  refine (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact Z_differentiableAt_of_ne ht
  · simpa only [Z, continuousAt_update_same] using riemannZeta_residue_one

/-- The open half-plane `re s > 1/2`. -/
def H : Set ℂ := {s | 1 / 2 < s.re}

lemma H_isOpen : IsOpen H := isOpen_lt continuous_const Complex.continuous_re

lemma H_convex : Convex ℝ H := convex_halfSpace_re_gt _

lemma H_isSimplyConnected : IsSimplyConnected H := by
  have : ContractibleSpace H := H_convex.contractibleSpace ⟨1, by norm_num [H]⟩
  exact SimplyConnectedSpace.ofContractible H

/-- Unconditional: a continuous branch of `log g` at a point where `g` is differentiable is
differentiable there. Precisely: if `f` is continuous at `z`, `g` is differentiable at `z`, and
`exp (f w) = g w` for `w` near `z`, then `f` is differentiable at `z`. -/
lemma differentiableAt_of_exp_eq {f g : ℂ → ℂ} {z : ℂ} (hf : ContinuousAt f z)
    (hg : DifferentiableAt ℂ g z) (hfg : ∀ᶠ w in 𝓝 z, exp (f w) = g w) :
    DifferentiableAt ℂ f z := by
  set w₀ := f z
  -- near `z`, `f w - w₀` has imaginary part in `(-π, π)`
  have hnear : ∀ᶠ w in 𝓝 z, ‖f w - w₀‖ < 1 := by
    have : Tendsto (fun w => f w - w₀) (𝓝 z) (𝓝 0) := by
      have h := hf.tendsto.sub (tendsto_const_nhds (x := w₀))
      rwa [sub_self] at h
    exact this.eventually (Metric.ball_mem_nhds 0 one_pos) |>.mono fun w hw => by
      simpa [dist_eq_norm] using hw
  have heq : f =ᶠ[𝓝 z] fun w => w₀ + log (g w * exp (-w₀)) := by
    filter_upwards [hnear, hfg] with w hw hwg
    have him : |(f w - w₀).im| < 1 := (abs_im_le_norm _).trans_lt hw
    have hpi : (1 : ℝ) < Real.pi := by linarith [Real.two_le_pi]
    rw [← hwg, ← exp_add, ← sub_eq_add_neg, log_exp (by linarith [abs_lt.1 him])
      (by linarith [abs_lt.1 him])]
    ring
  have hz1 : g z * exp (-w₀) = 1 := by
    have : exp (f z) = g z := hfg.self_of_nhds
    rw [← this, ← exp_add]; simp [w₀]
  have hslit : g z * exp (-w₀) ∈ slitPlane := by rw [hz1]; exact one_mem_slitPlane
  have hd : DifferentiableAt ℂ (fun w => w₀ + log (g w * exp (-w₀))) z :=
    (differentiableAt_const _).add ((hg.mul_const _).clog hslit)
  exact hd.congr_of_eventuallyEq heq

/-- **Step 1 of the converse (only this step is proved).** Under RH there is a holomorphic
logarithm of `Z(s) = (s - 1) ζ(s)` on the half-plane `re s > 1/2`; conversely, such a logarithm
forces RH. Exact statement: `RiemannHypothesis ↔ ∃ L, L` is complex-differentiable on
`{s | 1/2 < re s}` and `exp (L s) = Z s` there. The converse direction uses only `exp (L s) = Z s`, not differentiability; the branch `L` is not normalized to the Dirichlet series of `log ζ`. -/
theorem RH_iff_exists_log :
    RiemannHypothesis ↔
      ∃ L : ℂ → ℂ, DifferentiableOn ℂ L H ∧ ∀ s : ℂ, 1 / 2 < s.re → exp (L s) = Z s := by
  rw [RH_iff_noZerosRightHalf]
  constructor
  · intro hnz
    have hZ0 : (0 : ℂ) ∉ Z '' H := by
      rintro ⟨s, hs, hZs⟩
      rcases eq_or_ne s 1 with rfl | hs1
      · rw [Z_one] at hZs; exact one_ne_zero hZs
      · rw [Z_of_ne hs1] at hZs
        rcases mul_eq_zero.1 hZs with h | h
        · exact hs1 (sub_eq_zero.1 h)
        · exact hnz s hs h
    obtain ⟨L, hLc, hLe⟩ := exists_continuousOn_eqOn_exp_comp H_isSimplyConnected H_isOpen
      Z_differentiable.continuous.continuousOn hZ0
    refine ⟨L, fun s hs => ?_, fun s hs => hLe hs⟩
    refine (differentiableAt_of_exp_eq (hLc.continuousAt (H_isOpen.mem_nhds hs))
      (Z_differentiable s) ?_).differentiableWithinAt
    filter_upwards [H_isOpen.mem_nhds hs] with w hw
    exact hLe hw
  · rintro ⟨L, -, hL⟩ s hs hz
    rcases eq_or_ne s 1 with rfl | hs1
    · exact riemannZeta_one_ne_zero hz
    · have := hL s hs
      rw [Z_of_ne hs1, hz, mul_zero] at this
      exact exp_ne_zero _ this

/-- Direction `→` of `RH_iff_exists_log`, stated separately. -/
theorem RH_imp_exists_log :
    RiemannHypothesis →
      ∃ L : ℂ → ℂ, DifferentiableOn ℂ L H ∧ ∀ s : ℂ, 1 / 2 < s.re → exp (L s) = Z s :=
  RH_iff_exists_log.mp

end TromboRHtoMertens

#print axioms TromboRHtoMertens.zeta_zero_in_strip
#print axioms TromboRHtoMertens.not_trivial_of_re_pos
#print axioms TromboRHtoMertens.zeta_one_sub_eq_zero
#print axioms TromboRHtoMertens.RH_iff_noZerosRightHalf
#print axioms TromboRHtoMertens.Z_of_ne
#print axioms TromboRHtoMertens.Z_one
#print axioms TromboRHtoMertens.Z_differentiableAt_of_ne
#print axioms TromboRHtoMertens.Z_differentiable
#print axioms TromboRHtoMertens.H_isOpen
#print axioms TromboRHtoMertens.H_convex
#print axioms TromboRHtoMertens.H_isSimplyConnected
#print axioms TromboRHtoMertens.differentiableAt_of_exp_eq
#print axioms TromboRHtoMertens.RH_iff_exists_log
#print axioms TromboRHtoMertens.RH_imp_exists_log
