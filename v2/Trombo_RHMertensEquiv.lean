import Trombo_Mertens
import Trombo_RHMertens

/-!
# `RiemannHypothesis ↔ MertensBound`

* `→` : `TromboRHMertens.RH_imp_mertensBound` (this milestone, files in `/home/claude/mlib5`).
* `←` : `TromboMertens.mertensBound_imp_RH` (`/home/claude/mlib3/Trombo_Mertens.lean`, copied
  unchanged to `/home/claude/mlib5/Trombo_Mertens.lean`).

`TromboMertens.MertensBound` and `TromboRHMertens.MertensBound` are the same proposition
(the two `mertensM` definitions are literally the same sum); `mertensBound_iff` checks this.
-/

namespace TromboRHMertensEquiv

/-- The two definitions of the Mertens function agree. -/
lemma mertensM_eq (x : ℝ) : TromboMertens.mertensM x = TromboPerron.mertensM x := rfl

/-- The two definitions of `MertensBound` agree. -/
lemma mertensBound_iff : TromboMertens.MertensBound ↔ TromboRHMertens.MertensBound := Iff.rfl

/-- **`RH ↔ MertensBound`** (Littlewood 1912): Mathlib's `RiemannHypothesis` holds iff for every
`ε > 0` there is `C` with `|M(x)| ≤ C x^(1/2+ε)` for all real `x ≥ 1`. -/
theorem RH_iff_mertensBound : RiemannHypothesis ↔ TromboMertens.MertensBound :=
  ⟨fun h => mertensBound_iff.mpr (TromboRHMertens.RH_imp_mertensBound h),
    TromboMertens.mertensBound_imp_RH⟩

end TromboRHMertensEquiv

#print axioms TromboRHMertensEquiv.mertensM_eq
#print axioms TromboRHMertensEquiv.mertensBound_iff
#print axioms TromboRHMertensEquiv.RH_iff_mertensBound
