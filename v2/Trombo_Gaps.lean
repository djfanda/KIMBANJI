import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Prime.Nth

/-!
# Trombo hypothesis ladder: prime gaps

Every open conjecture below is a `def … : Prop`; nothing is assumed as an axiom.
Every theorem has the shape `Hypothesis → Conclusion`.

`pr k = Nat.nth Nat.Prime k` is the `k`-th prime, indexed from `0` (`pr 0 = 2`).
-/

open Real Filter

namespace TromboGaps

/-- The `k`-th prime, `pr 0 = 2`. -/
noncomputable abbrev pr (k : ℕ) : ℕ := Nat.nth Nat.Prime k

/-- There is a prime strictly between `n^2` and `(n+1)^2`. -/
def LegendreAt (n : ℕ) : Prop := ∃ p, p.Prime ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2

/-- Legendre's conjecture (open): for every `n ≥ 1` there is a prime in `(n^2, (n+1)^2)`. -/
def Legendre : Prop := ∀ n : ℕ, 1 ≤ n → LegendreAt n

/-- Oppermann's conjecture (open): for every `n > 1` there is a prime in `(n^2 - n, n^2)`
and a prime in `(n^2, n^2 + n)`. -/
def Oppermann : Prop :=
  ∀ n : ℕ, 1 < n →
    (∃ p, p.Prime ∧ n ^ 2 - n < p ∧ p < n ^ 2) ∧ (∃ p, p.Prime ∧ n ^ 2 < p ∧ p < n ^ 2 + n)

/-- Andrica's inequality at index `k`: `√p_{k+1} - √p_k < 1`. -/
def AndricaAt (k : ℕ) : Prop := √(pr (k + 1) : ℝ) - √(pr k : ℝ) < 1

/-- Andrica's conjecture (open): `√p_{k+1} - √p_k < 1` for every `k`. -/
def Andrica : Prop := ∀ k : ℕ, AndricaAt k

/-- Cramér-type gap bound with constant `C` (open for every `C`): from some index on,
`p_{k+1} - p_k ≤ C · (log p_k)^2`. -/
def Cramer (C : ℝ) : Prop :=
  ∃ K : ℕ, ∀ k, K ≤ k → ((pr (k + 1) : ℝ) - pr k) ≤ C * (Real.log (pr k)) ^ 2

/-! ## Auxiliary facts about consecutive primes (unconditional) -/

/-- For `N ≥ 2` there is an index `k` with `p_k ≤ N < p_{k+1}`; moreover `K ≤ k`
for every `K` with `p_K ≤ N`. -/
lemma bracket (N : ℕ) (hN : 2 ≤ N) :
    ∃ k, pr k ≤ N ∧ N < pr (k + 1) ∧ ∀ K, pr K ≤ N → K ≤ k := by
  have hinf := Nat.infinite_setOfPred_prime
  obtain ⟨m, hm⟩ : ∃ m, m = Nat.count Nat.Prime (N + 1) := ⟨_, rfl⟩
  have key : ∀ a, a < m ↔ Nat.nth Nat.Prime a < N + 1 := fun a => by
    rw [hm]; exact Nat.lt_nth_iff_count_lt hinf
  have hup : N + 1 ≤ Nat.nth Nat.Prime m := by
    rw [hm]; exact Nat.le_nth_count hinf (N + 1)
  have hm0 : 0 < m := (key 0).2 (by rw [Nat.nth_prime_zero_eq_two]; omega)
  refine ⟨m - 1, ?_, ?_, ?_⟩
  · have := (key (m - 1)).1 (by omega)
    show Nat.nth Nat.Prime (m - 1) ≤ N
    omega
  · have : m - 1 + 1 = m := by omega
    show N < Nat.nth Nat.Prime (m - 1 + 1)
    rw [this]; omega
  · intro K hK
    have hK' : Nat.nth Nat.Prime K ≤ N := hK
    have := (key K).2 (by omega)
    omega

/-- `p_k ≥ k + 2`. -/
lemma pr_ge (k : ℕ) : k + 2 ≤ pr k := Nat.add_two_le_nth_prime k

/-! ## (a) Oppermann ⇒ Legendre -/

/-- Oppermann's conjecture implies Legendre's conjecture. -/
theorem oppermann_imp_legendre : Oppermann → Legendre := by
  intro hO n hn
  rcases Nat.lt_or_ge 1 n with h | h
  · obtain ⟨p, hp, h1, h2⟩ := (hO n h).2
    exact ⟨p, hp, h1, by nlinarith⟩
  · have : n = 1 := by omega
    subst this
    exact ⟨2, Nat.prime_two, by norm_num, by norm_num⟩

/-! ## (b) Andrica ⇒ gap bound -/

/-- If `√q - √p < 1` with `0 ≤ p, q` then `q - p < 2√p + 1`. -/
lemma gap_of_sqrt_diff {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (h : √q - √p < 1) :
    q - p < 2 * √p + 1 := by
  have h1 := Real.sq_sqrt hp
  have h2 := Real.sq_sqrt hq
  have h3 := Real.sqrt_nonneg q
  have h4 := Real.sqrt_nonneg p
  nlinarith

/-- Andrica's conjecture implies `p_{k+1} - p_k < 2√p_k + 1` for every `k`. -/
theorem andrica_imp_gap_bound :
    Andrica → ∀ k, ((pr (k + 1) : ℝ) - pr k) < 2 * √(pr k : ℝ) + 1 := by
  intro hA k
  exact gap_of_sqrt_diff (Nat.cast_nonneg _) (Nat.cast_nonneg _) (hA k)

/-! ## (c) Andrica ⇒ Legendre -/

/-- If some index `k` has `p_k ≤ n^2 < p_{k+1}` and Andrica holds at `k`,
then there is a prime in `(n^2, (n+1)^2)`. -/
lemma legendreAt_of_bracket {n k : ℕ} (h1 : pr k ≤ n ^ 2) (h2 : n ^ 2 < pr (k + 1))
    (hA : AndricaAt k) : LegendreAt n := by
  by_cases hq : pr (k + 1) < (n + 1) ^ 2
  · exact ⟨pr (k + 1), Nat.prime_nth_prime _, h2, hq⟩
  · exfalso
    push Not at hq
    have hq' : ((n + 1 : ℕ) : ℝ) ^ 2 ≤ (pr (k + 1) : ℝ) := by exact_mod_cast hq
    have hp' : (pr k : ℝ) ≤ ((n : ℕ) : ℝ) ^ 2 := by exact_mod_cast h1
    have e1 : ((n + 1 : ℕ) : ℝ) ≤ √(pr (k + 1) : ℝ) := by
      have := Real.sqrt_le_sqrt hq'
      rwa [Real.sqrt_sq (Nat.cast_nonneg _)] at this
    have e2 : √(pr k : ℝ) ≤ ((n : ℕ) : ℝ) := by
      have := Real.sqrt_le_sqrt hp'
      rwa [Real.sqrt_sq (Nat.cast_nonneg _)] at this
    have : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    unfold AndricaAt at hA
    linarith

/-- Andrica's conjecture implies Legendre's conjecture. -/
theorem andrica_imp_legendre : Andrica → Legendre := by
  intro hA n hn
  rcases Nat.lt_or_ge 1 n with h | h
  · obtain ⟨k, h1, h2, -⟩ := bracket (n ^ 2) (by nlinarith)
    exact legendreAt_of_bracket h1 h2 (hA k)
  · have : n = 1 := by omega
    subst this
    exact ⟨2, Nat.prime_two, by norm_num, by norm_num⟩

/-! ## (d) Cramér ⇒ Legendre for all large `n` -/

/-- For every `C > 0`, eventually `4C·(log x)^2 ≤ x`. -/
lemma eventually_log_sq_le (C : ℝ) (hC : 0 < C) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → 4 * C * (Real.log x) ^ 2 ≤ x := by
  have h := (isLittleO_pow_log_id_atTop (n := 2)).bound (c := 1 / (4 * C)) (by positivity)
  obtain ⟨X, hX⟩ := eventually_atTop.1 h
  refine ⟨max X 0, fun x hx => ?_⟩
  have hx0 : 0 ≤ x := le_trans (le_max_right _ _) hx
  have := hX x (le_trans (le_max_left _ _) hx)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), id,
    abs_of_nonneg hx0] at this
  have h4C : 0 < 4 * C := by positivity
  calc 4 * C * Real.log x ^ 2 ≤ 4 * C * (1 / (4 * C) * x) := by gcongr
    _ = x := by field_simp

/-- For any constant `C > 0`, Cramér's bound `Cramer C` implies that Legendre's statement
holds for every sufficiently large `n`. -/
theorem cramer_imp_legendre_eventually (C : ℝ) (hC : 0 < C) :
    Cramer C → ∃ N : ℕ, ∀ n, N ≤ n → LegendreAt n := by
  rintro ⟨K, hK⟩
  obtain ⟨X, hX⟩ := eventually_log_sq_le C hC
  refine ⟨max (max 2 (pr K)) ⌈X⌉₊, fun n hn => ?_⟩
  have hn2 : 2 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnK : pr K ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hnX : X ≤ (n : ℝ) :=
    le_trans (Nat.le_ceil X) (by exact_mod_cast le_trans (le_max_right _ _) hn)
  have hnn : n ≤ n ^ 2 := by nlinarith
  obtain ⟨k, h1, h2, h3⟩ := bracket (n ^ 2) (by nlinarith)
  have hk : K ≤ k := h3 K (le_trans hnK hnn)
  have hgap := hK k hk
  -- bound on log p_k
  have hp2 : (2 : ℝ) ≤ pr k := by exact_mod_cast (Nat.prime_nth_prime k).two_le
  have hp1 : (pr k : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast h1
  have hlogp0 : 0 ≤ Real.log (pr k) := Real.log_nonneg (by linarith)
  have hlogp : Real.log (pr k) ≤ 2 * Real.log n := by
    have e : Real.log ((n : ℝ) ^ 2) = 2 * Real.log n := by rw [Real.log_pow]; norm_num
    rw [← e]; exact Real.log_le_log (by linarith) hp1
  have hsq : Real.log (pr k) ^ 2 ≤ 4 * Real.log n ^ 2 := by nlinarith
  have hX' := hX n hnX
  have hgap' : ((pr (k + 1) : ℝ)) ≤ (n : ℝ) ^ 2 + n := by nlinarith
  have hlt : pr (k + 1) < (n + 1) ^ 2 := by
    have : ((pr (k + 1) : ℕ) : ℝ) < ((n + 1) ^ 2 : ℕ) := by push_cast; nlinarith
    exact_mod_cast this
  exact ⟨pr (k + 1), Nat.prime_nth_prime _, h2, hlt⟩

/-! ## (e) Cramér ⇒ Andrica for all large `k` -/

/-- For any constant `C > 0`, Cramér's bound `Cramer C` implies Andrica's inequality
`√p_{k+1} - √p_k < 1` for every sufficiently large `k`. -/
theorem cramer_imp_andrica_eventually (C : ℝ) (hC : 0 < C) :
    Cramer C → ∃ K' : ℕ, ∀ k, K' ≤ k → AndricaAt k := by
  rintro ⟨K, hK⟩
  obtain ⟨X, hX⟩ := eventually_log_sq_le C hC
  refine ⟨max K ⌈X ^ 2⌉₊, fun k hk => ?_⟩
  have hkK : K ≤ k := le_trans (le_max_left _ _) hk
  have hgap := hK k hkK
  obtain ⟨p, hpdef⟩ : ∃ p : ℝ, p = (pr k : ℝ) := ⟨_, rfl⟩
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = (pr (k + 1) : ℝ) := ⟨_, rfl⟩
  rw [← hpdef, ← hqdef] at hgap
  have hp2 : (2 : ℝ) ≤ p := by rw [hpdef]; exact_mod_cast (Nat.prime_nth_prime k).two_le
  have hq0 : 0 ≤ q := by rw [hqdef]; exact Nat.cast_nonneg _
  -- √p ≥ X
  have hpk : (k : ℝ) ≤ p := by
    have := pr_ge k; rw [hpdef]; exact_mod_cast (by omega : k ≤ pr k)
  have hkX : X ^ 2 ≤ (k : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hk)
  have hsX : X ≤ √p := le_trans (le_abs_self X) (Real.abs_le_sqrt (le_trans hkX hpk))
  have hs := hX (√p) hsX
  have hlog : Real.log p = 2 * Real.log (√p) := by
    rw [Real.log_sqrt (by linarith)]; ring
  have hgap' : q - p ≤ √p := by
    calc q - p ≤ C * Real.log p ^ 2 := hgap
      _ = 4 * C * Real.log (√p) ^ 2 := by rw [hlog]; ring
      _ ≤ √p := hs
  have e1 := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ p)
  have e2 := Real.sq_sqrt hq0
  have e3 : 0 < √p := Real.sqrt_pos.2 (by linarith)
  have e4 := Real.sqrt_nonneg q
  show √(pr (k + 1) : ℝ) - √(pr k : ℝ) < 1
  rw [← hpdef, ← hqdef]
  by_contra hcon
  push Not at hcon
  nlinarith

/-! ## Caveat: the constant matters if the bound is required for all `p ≥ 3` -/

/-- The uniform form "for all `k ≥ 1`, `p_{k+1} - p_k ≤ 1 · (log p_k)^2`" is false:
at `k = 1`, `p_2 - p_1 = 5 - 3 = 2 > (log 3)^2`. -/
theorem cramer_one_uniform_false :
    ¬ ∀ k, 1 ≤ k → ((pr (k + 1) : ℝ) - pr k) ≤ 1 * (Real.log (pr k)) ^ 2 := by
  intro h
  have h1 := h 1 le_rfl
  simp only [pr, Nat.nth_prime_one_eq_three] at h1
  have hl0 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hl : Real.log 3 < 2 * 0.6931471808 := by
    have : Real.log 3 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
    have e : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith [Real.log_two_lt_d9]
  norm_num at h1
  nlinarith

end TromboGaps

#print axioms TromboGaps.bracket
#print axioms TromboGaps.pr_ge
#print axioms TromboGaps.oppermann_imp_legendre
#print axioms TromboGaps.gap_of_sqrt_diff
#print axioms TromboGaps.andrica_imp_gap_bound
#print axioms TromboGaps.legendreAt_of_bracket
#print axioms TromboGaps.andrica_imp_legendre
#print axioms TromboGaps.eventually_log_sq_le
#print axioms TromboGaps.cramer_imp_legendre_eventually
#print axioms TromboGaps.cramer_imp_andrica_eventually
#print axioms TromboGaps.cramer_one_uniform_false
