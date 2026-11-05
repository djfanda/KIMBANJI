import Trombo_PerronVendor
import Trombo_ZetaLogBound
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Item 1: truncated Perron formula for the Möbius function

Specialises Tau Ceti's `TauCeti.norm_truncatedPerron_LSeries_sub_sum_le` (vendored in
`Trombo_PerronVendor.lean`) to `f = μ`, using `L(μ, s) = 1/ζ(s)` for `re s > 1`, and identifies the
sharp partial sum with the Mertens function `M(x) = ∑_{1 ≤ n ≤ x} μ(n)` at non-integral `x > 0`.

Exact statements: see `perron_moebius` and `mertensM_perron`. No growth estimate for the error
series is proved here (that is part of the assembly, item 7).
-/

open Complex ArithmeticFunction
open scoped LSeries.notation ArithmeticFunction.Moebius Real

namespace TromboPerron

/-- The Mertens function `M(x) = ∑_{1 ≤ n ≤ x} μ(n)` (identical to `TromboMertens.mertensM`). -/
noncomputable def mertensM (x : ℝ) : ℤ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, μ n

/-- `L(μ, s) = ζ(s)⁻¹` for `re s > 1`. -/
lemma LSeries_moebius_eq_inv_zeta {s : ℂ} (hs : 1 < s.re) : L ↗μ s = (riemannZeta s)⁻¹ := by
  have h := LSeries_zeta_mul_Lseries_moebius hs
  rw [LSeries_zeta_eq_riemannZeta hs] at h
  exact (inv_eq_of_mul_eq_one_right h).symm

/-- **Item 1 (Perron for μ).** For `x > 0` not an integer, `c > 1`, `T > 0`:
`‖(2π)⁻¹ ∫_{-T}^{T} ζ(c+it)⁻¹ x^{c+it}/(c+it) dt − ∑_{1 ≤ n < ⌈x⌉} μ(n)‖
  ≤ ∑' n, ‖μ(n)‖ (x/n)^c / (π T |log(x/n)|)`. -/
theorem perron_moebius {x c T : ℝ} (hx : 0 < x) (hc : 1 < c) (hT : 0 < T)
    (hoff : ∀ n : ℕ, x ≠ n) :
    ‖(((2 * π : ℝ) : ℂ)⁻¹ * ∫ t in -T..T,
        (riemannZeta ((c : ℂ) + t * I))⁻¹ * TauCeti.perronIntegrand x c t)
        - ∑ n ∈ Finset.Ico 1 ⌈x⌉₊, ((μ n : ℤ) : ℂ)‖
      ≤ ∑' n : ℕ, ‖((μ n : ℤ) : ℂ)‖ * ((x / n) ^ c / (π * T * |Real.log (x / n)|)) := by
  have hsum : LSeriesSummable ↗μ (c : ℂ) := LSeriesSummable_moebius_iff.mpr (by simpa using hc)
  have h := TauCeti.norm_truncatedPerron_LSeries_sub_sum_le (f := ↗μ) hx (by linarith) hT
    (fun n _ => hoff n) hsum
  have heq : (fun t : ℝ => L ↗μ ((c : ℂ) + t * I) * TauCeti.perronIntegrand x c t) =
      fun t : ℝ => (riemannZeta ((c : ℂ) + t * I))⁻¹ * TauCeti.perronIntegrand x c t := by
    funext t
    rw [LSeries_moebius_eq_inv_zeta (by simpa using hc)]
  rw [heq] at h
  exact h

/-- For non-integral `x > 0`, `⌈x⌉₊ = ⌊x⌋₊ + 1`. -/
lemma ceil_eq_floor_add_one {x : ℝ} (hx : 0 < x) (hoff : ∀ n : ℕ, x ≠ n) :
    ⌈x⌉₊ = ⌊x⌋₊ + 1 := by
  rw [Nat.ceil_eq_iff (by omega)]
  refine ⟨?_, ?_⟩
  · simp only [Nat.add_sub_cancel]
    exact lt_of_le_of_ne (Nat.floor_le hx.le) (fun h => hoff _ h.symm)
  · push_cast
    exact (Nat.lt_floor_add_one x).le

/-- For non-integral `x > 0`, `∑_{1 ≤ n < ⌈x⌉} μ(n) = M(x)`. -/
lemma sum_Ico_ceil_eq_mertensM {x : ℝ} (hx : 0 < x) (hoff : ∀ n : ℕ, x ≠ n) :
    ∑ n ∈ Finset.Ico 1 ⌈x⌉₊, ((μ n : ℤ) : ℂ) = ((mertensM x : ℤ) : ℂ) := by
  rw [ceil_eq_floor_add_one hx hoff, mertensM, Finset.Ico_add_one_right_eq_Icc]
  push_cast
  rfl

/-- **Item 1, Mertens form.** For `x > 0` not an integer, `c > 1`, `T > 0`:
`‖(2π)⁻¹ ∫_{-T}^{T} ζ(c+it)⁻¹ x^{c+it}/(c+it) dt − M(x)‖
  ≤ ∑' n, ‖μ(n)‖ (x/n)^c / (π T |log(x/n)|)`. -/
theorem mertensM_perron {x c T : ℝ} (hx : 0 < x) (hc : 1 < c) (hT : 0 < T)
    (hoff : ∀ n : ℕ, x ≠ n) :
    ‖(((2 * π : ℝ) : ℂ)⁻¹ * ∫ t in -T..T,
        (riemannZeta ((c : ℂ) + t * I))⁻¹ * TauCeti.perronIntegrand x c t)
        - ((mertensM x : ℤ) : ℂ)‖
      ≤ ∑' n : ℕ, ‖((μ n : ℤ) : ℂ)‖ * ((x / n) ^ c / (π * T * |Real.log (x / n)|)) := by
  rw [← sum_Ico_ceil_eq_mertensM hx hoff]
  exact perron_moebius hx hc hT hoff

end TromboPerron

#print axioms TromboPerron.LSeries_moebius_eq_inv_zeta
#print axioms TromboPerron.perron_moebius
#print axioms TromboPerron.ceil_eq_floor_add_one
#print axioms TromboPerron.sum_Ico_ceil_eq_mertensM
#print axioms TromboPerron.mertensM_perron
