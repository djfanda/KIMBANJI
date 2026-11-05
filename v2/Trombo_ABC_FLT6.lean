import Mathlib.NumberTheory.FLT.Basic
import Mathlib.RingTheory.Radical.NatInt

/-!
# Trombo certificate, rung 3: an explicit abc hypothesis implies FLT for coprime solutions, exponents `n ≥ 6`

`ABCExplicit` is a **definition of a proposition** (not an axiom, not assumed anywhere globally):
for all coprime positive naturals `a, b` with `c = a + b`, `c < rad(a·b·c)^2`.

The form "c < rad(abc)^2" was conjectured by Granville and Tucker ("It's as easy as abc",
Notices AMS 49 (2002)); see also Laishram–Shorey, Acta Arith. 154 (2012).

`flt_ge_six_of_abcExplicit` proves the implication
`ABCExplicit → ∀ n ≥ 6, ∀ a b c, 0 < a → 0 < b → 0 < c → Coprime a b → a^n + b^n ≠ c^n`.

Nothing here proves `ABCExplicit` itself; it is an open conjecture. Fermat's Last Theorem is
itself a theorem (Wiles 1995, Taylor–Wiles). Anthropic announced on 2026-09-04 an end-to-end Lean
formalisation of FLT (https://www.anthropic.com/research/formalizing-fermats-last-theorem); that
work is not used or checked here. This rung is
only a demonstration of the "hypothesis as a `Prop`" method: the conditional statement is
machine-checked, the hypothesis is not.
-/

open UniqueFactorizationMonoid

/-- The explicit abc hypothesis (stated as a `Prop`, not assumed): for all coprime positive
naturals `a, b` and `c = a + b`, one has `c < (radical (a * b * c))^2`. -/
def ABCExplicit : Prop :=
  ∀ a b c : ℕ, 0 < a → 0 < b → Nat.Coprime a b → c = a + b → c < (radical (a * b * c)) ^ 2

/-- `rad (x^n) ≤ x` for `x ≠ 0`, `n ≠ 0`. -/
lemma radical_pow_le_self {x n : ℕ} (hx : x ≠ 0) (hn : n ≠ 0) : radical (x ^ n) ≤ x := by
  rw [radical_pow x hn]
  exact Nat.radical_le_self_iff.mpr hx

/-- **abc ⇒ FLT for n ≥ 6.** Under the hypothesis `ABCExplicit`, for every exponent `n ≥ 6`
and all positive naturals `a, b, c` with `gcd(a, b) = 1`, `a^n + b^n ≠ c^n`.
Proof: apply the hypothesis to `(aⁿ, bⁿ, cⁿ)`; `rad(aⁿbⁿcⁿ) = rad(abc) ≤ abc < c³`,
so `cⁿ < c⁶ ≤ cⁿ`, a contradiction. -/
theorem flt_ge_six_of_abcExplicit (habc : ABCExplicit) :
    ∀ n ≥ 6, ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c → Nat.Coprime a b → a ^ n + b ^ n ≠ c ^ n := by
  intro n hn a b c ha hb hc hcop heq
  have hn0 : n ≠ 0 := by omega
  -- a < c and b < c
  have hac : a < c := by
    have : a ^ n < c ^ n := by rw [← heq]; exact Nat.lt_add_of_pos_right ((Nat.pow_pos (n := n) hb))
    exact (Nat.pow_lt_pow_iff_left hn0).mp this
  have hbc : b < c := by
    have : b ^ n < c ^ n := by rw [← heq]; exact Nat.lt_add_of_pos_left ((Nat.pow_pos (n := n) ha))
    exact (Nat.pow_lt_pow_iff_left hn0).mp this
  have hc2 : 2 ≤ c := by omega
  -- apply the hypothesis to (aⁿ, bⁿ, cⁿ)
  have h := habc (a ^ n) (b ^ n) (c ^ n) ((Nat.pow_pos (n := n) ha)) ((Nat.pow_pos (n := n) hb))
    (Nat.Coprime.pow n n hcop) heq.symm
  rw [← mul_pow, ← mul_pow] at h
  have habc0 : a * b * c ≠ 0 := by positivity
  have hrad : radical ((a * b * c) ^ n) ≤ a * b * c := radical_pow_le_self habc0 hn0
  have hprod : a * b * c < c ^ 3 := by
    have h1 : a * b < c * c := Nat.mul_lt_mul'' hac hbc
    calc a * b * c < c * c * c := Nat.mul_lt_mul_of_pos_right h1 hc
      _ = c ^ 3 := by ring
  have h6 : (radical ((a * b * c) ^ n)) ^ 2 < c ^ 6 := by
    calc (radical ((a * b * c) ^ n)) ^ 2 ≤ (a * b * c) ^ 2 := Nat.pow_le_pow_left hrad 2
      _ < (c ^ 3) ^ 2 := Nat.pow_lt_pow_left hprod (by norm_num)
      _ = c ^ 6 := by ring
  have hcn : c ^ 6 ≤ c ^ n := Nat.pow_le_pow_right (by omega) hn
  omega

#print axioms radical_pow_le_self
#print axioms flt_ge_six_of_abcExplicit

theorem fermatLastTheoremFor_of_abcExplicit (habc : ABCExplicit) (n : ℕ) (hn : 6 ≤ n) :
    FermatLastTheoremFor n := by
  intro a b c ha hb hc heq
  have hn0 : n ≠ 0 := by omega
  have hd0 : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero ha)
  have hcop : Nat.Coprime (a / Nat.gcd a b) (b / Nat.gcd a b) := Nat.coprime_div_gcd_div_gcd hd0
  obtain ⟨a', ha'⟩ : Nat.gcd a b ∣ a := Nat.gcd_dvd_left a b
  obtain ⟨b', hb'⟩ : Nat.gcd a b ∣ b := Nat.gcd_dvd_right a b
  generalize Nat.gcd a b = d at hd0 hcop ha' hb'
  subst ha' hb'
  rw [Nat.mul_div_cancel_left _ hd0, Nat.mul_div_cancel_left _ hd0] at hcop
  have hdc : d ∣ c := by
    have : d ^ n ∣ c ^ n := ⟨a' ^ n + b' ^ n, by rw [← heq]; ring⟩
    exact (Nat.pow_dvd_pow_iff hn0).mp this
  obtain ⟨c', rfl⟩ := hdc
  have heq' : a' ^ n + b' ^ n = c' ^ n := by
    have h1 : d ^ n * (a' ^ n + b' ^ n) = d ^ n * c' ^ n := by
      rw [mul_add, ← mul_pow, ← mul_pow, ← mul_pow]; exact heq
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
  exact flt_ge_six_of_abcExplicit habc n hn a' b' c'
    (Nat.pos_of_ne_zero (right_ne_zero_of_mul ha)) (Nat.pos_of_ne_zero (right_ne_zero_of_mul hb))
    (Nat.pos_of_ne_zero (right_ne_zero_of_mul hc)) hcop heq'
#print axioms fermatLastTheoremFor_of_abcExplicit
