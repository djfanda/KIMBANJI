import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Basic

/-!
# Trombo hypothesis ladder: Hardy–Littlewood (pair form) ⇒ Polignac (weak) / twin primes

Open conjectures are `def … : Prop`; nothing is assumed as an axiom.
Every theorem has the shape `Hypothesis → Conclusion`.
-/

open Real Filter

namespace TromboHL

/-- `pairCount k x = #{p ≤ x : p prime and p + k prime}`. -/
def pairCount (k x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter (fun p => p.Prime ∧ (p + k).Prime)).card

/-- Lower-bound form of the Hardy–Littlewood conjecture for the pair `(p, p + k)` (open for
every even `k > 0`): there are `c > 0` and `N` with
`c · x / (log x)^2 ≤ pairCount k x` for every natural `x ≥ N`.
This is weaker than the asymptotic `pairCount k x ∼ 𝔖(k) · x / (log x)^2`. -/
def HL_pair (k : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ x : ℕ, N ≤ x →
    c * x / (Real.log x) ^ 2 ≤ (pairCount k x : ℝ)

/-- There are infinitely many primes `p` with `p + k` also prime. -/
def InfinitelyManyPairs (k : ℕ) : Prop := ∀ N : ℕ, ∃ p, N < p ∧ p.Prime ∧ (p + k).Prime

/-- Weak Polignac statement (open): for every even `k > 0` there are infinitely many primes `p`
with `p + k` prime. The two primes need NOT be consecutive; the consecutive version
(`p + k` is the next prime after `p`) is a strictly stronger claim and is not treated here. -/
def PolignacWeak : Prop := ∀ k : ℕ, 0 < k → Even k → InfinitelyManyPairs k

/-- Twin prime conjecture (open): infinitely many primes `p` with `p + 2` prime. -/
def TwinPrime : Prop := ∀ N : ℕ, ∃ p, N < p ∧ p.Prime ∧ (p + 2).Prime

/-- If no prime `p > N` has `p + k` prime, then `pairCount k x ≤ N + 1` for every `x`. -/
lemma pairCount_le_of_none {k N : ℕ} (h : ∀ p, N < p → p.Prime → ¬ (p + k).Prime) (x : ℕ) :
    pairCount k x ≤ N + 1 := by
  unfold pairCount
  calc ((Finset.range (x + 1)).filter (fun p => p.Prime ∧ (p + k).Prime)).card
      ≤ (Finset.range (N + 1)).card := by
        apply Finset.card_le_card
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
        by_contra hpN
        exact h p (by omega) hp.2.1 hp.2.2
    _ = N + 1 := Finset.card_range _

/-- For every `c > 0` and every real `B`, eventually `B < c · x / (log x)^2` on the naturals. -/
lemma unbounded (c : ℝ) (hc : 0 < c) (B : ℝ) :
    ∃ X : ℕ, ∀ x : ℕ, X ≤ x → B < c * x / (Real.log x) ^ 2 := by
  have hB : 0 < |B| + 1 := by positivity
  have h := (isLittleO_pow_log_id_atTop (n := 2)).bound (c := c / (|B| + 1)) (by positivity)
  obtain ⟨X0, hX0⟩ := eventually_atTop.1 h
  refine ⟨max 3 ⌈X0⌉₊, fun x hx => ?_⟩
  have hx3 : (3 : ℝ) ≤ x := by exact_mod_cast le_trans (le_max_left _ _) hx
  have hxX : X0 ≤ (x : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hx)
  have hb := hX0 x hxX
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), id,
    abs_of_nonneg (show (0 : ℝ) ≤ (x : ℝ) by positivity)] at hb
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hl2 : 0 < Real.log x ^ 2 := by positivity
  have key : (|B| + 1) * Real.log x ^ 2 ≤ c * x := by
    calc (|B| + 1) * Real.log x ^ 2 ≤ (|B| + 1) * (c / (|B| + 1) * x) := by gcongr
      _ = c * x := by field_simp
  calc B < |B| + 1 := by linarith [le_abs_self B]
    _ ≤ c * x / Real.log x ^ 2 := by rw [le_div_iff₀ hl2]; exact key

/-- The Hardy–Littlewood lower bound for the pair `(p, p + k)` implies that there are
infinitely many primes `p` with `p + k` prime. -/
theorem hl_pair_imp_infinitelyMany (k : ℕ) : HL_pair k → InfinitelyManyPairs k := by
  rintro ⟨c, hc, N1, hN1⟩ N
  by_contra hcon
  have h : ∀ p, N < p → p.Prime → ¬ (p + k).Prime := by
    intro p hp hpp hpk
    exact hcon ⟨p, hp, hpp, hpk⟩
  obtain ⟨X, hX⟩ := unbounded c hc ((N : ℝ) + 1)
  set x := max X N1
  have h1 := hX x (le_max_left _ _)
  have h2 := hN1 x (le_max_right _ _)
  have h3 : (pairCount k x : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast pairCount_le_of_none h x
  linarith

/-- If the Hardy–Littlewood lower bound holds for every even `k > 0`, then the weak Polignac
statement holds (pairs need not be consecutive primes). -/
theorem hl_all_imp_polignacWeak :
    (∀ k : ℕ, 0 < k → Even k → HL_pair k) → PolignacWeak :=
  fun h k hk he => hl_pair_imp_infinitelyMany k (h k hk he)

/-- The Hardy–Littlewood lower bound for `k = 2` implies the twin prime conjecture. -/
theorem hl_two_imp_twinPrime : HL_pair 2 → TwinPrime :=
  hl_pair_imp_infinitelyMany 2

end TromboHL

#print axioms TromboHL.pairCount_le_of_none
#print axioms TromboHL.unbounded
#print axioms TromboHL.hl_pair_imp_infinitelyMany
#print axioms TromboHL.hl_all_imp_polignacWeak
#print axioms TromboHL.hl_two_imp_twinPrime
