import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Trombo hypothesis ladder: GRH ⇒ RH

`GRH` is a `def … : Prop` (open); nothing is assumed as an axiom.
The target is Mathlib's own `RiemannHypothesis`.

Convention: `GRH` speaks only about zeros in the open critical strip `0 < re s < 1`.
This avoids the junk value of `LFunction χ` at the pole `s = 1` (trivial `χ`) and the zeros on
`re s = 0` that imprimitive characters acquire from their missing Euler factors.
-/

open Complex Real

namespace TromboGRH

/-- Generalized Riemann Hypothesis for Dirichlet L-functions (open), critical-strip form:
for every modulus `q ≥ 1`, every Dirichlet character `χ` mod `q`, and every `s` with
`0 < re s < 1`, `L(χ, s) = 0` implies `re s = 1/2`. -/
def GRH : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
    DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2

/-- Unconditional: a zero `s ≠ 1` of `ζ` that is not of the form `-2(n+1)` lies in the open
critical strip `0 < re s < 1`. -/
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
    have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
    have hA : (2 : ℂ) * (2 * π) ^ (-w) ≠ 0 := by
      refine mul_ne_zero two_ne_zero ?_
      rw [cpow_def_of_ne_zero (mul_ne_zero two_ne_zero hpi)]
      exact exp_ne_zero _
    have hG : Gamma w ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
    have hZ : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re hwre
    have hcos : cos (π * w / 2) = 0 := by
      by_contra hc
      exact (mul_ne_zero (mul_ne_zero (mul_ne_zero hA hG) hc) hZ) hfe.symm
    obtain ⟨k, hk⟩ := cos_eq_zero_iff.1 hcos
    have hwk : w = 2 * k + 1 := by
      have : π * w = π * (2 * k + 1) := by linear_combination 2 * hk
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

/-- GRH (critical-strip form, all Dirichlet characters) implies Mathlib's
`RiemannHypothesis`; only the character mod `1` is used. -/
theorem grh_imp_rh : GRH → RiemannHypothesis := by
  intro hG s hz htriv _hs1
  obtain ⟨h0, h1⟩ := zeta_zero_in_strip hz htriv
  have hL : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) s = 0 := by
    rw [DirichletCharacter.LFunction_modOne_eq]; exact hz
  exact hG 1 1 s hL h0 h1

end TromboGRH

#print axioms TromboGRH.zeta_zero_in_strip
#print axioms TromboGRH.grh_imp_rh
