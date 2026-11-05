/-!
# 견본 — 흐름 + 단조량 + 수술 + 유한 소멸 (페렐만/해밀턴 틀의 이산 뼈대)

이 파일은 견본의 논리 뼈대이다. 리만 가설에 대해 아무것도 증명하지 않는다.
리치 흐름에 대해서도 아무것도 증명하지 않는다.

* Template : 이산 시간 t : Nat · 음 아닌 양 W · 살아 있음 alive.
  살아 있는 동안 W 가 매 걸음 δ ≥ 1 이상 줄면 유한 시간 안에 소멸한다.
  수술 걸음에서는 W 가 늘지 않기만 하고, 대신 두 번째 예산 V 를 ε ≥ 1 이상 쓴다.
  그러면 수술 횟수는 V 0 / ε 이하이고, 소멸 시각은 W 0 / δ + V 0 / ε 이하이다.
* RHSlot : 드 브라윈–뉴먼 꼴의 조건부 정리. nonreal k = 시각 k 에서 실수 아닌 영점의 수 (추상 함수).
  (H_end) 끝 시각 T0 에서 nonreal T0 = 0 (알려진 상계 Λ ≤ 0.2 의 자리) ·
  (H_back) 뒤로 가는 단조성 ∀ k < T0, nonreal k ≤ nonreal (k+1).
  두 가정이 있으면 nonreal 0 = 0.
  H_back 이 바로 비어 있는 단조량 — 알려진 열 흐름 동역학은 반대 방향만 준다(로저스–타오 Λ ≥ 0).
  H_end 만으로는 결론이 나오지 않는다 (반례 slot_needs_monotone) ·
  앞으로 가는 단조성 nonreal (k+1) ≤ nonreal k 를 더해도 나오지 않는다 (forward_monotone_insufficient).
-/

namespace Template

/-! ## 1. 유한 소멸 -/

/-- 처음 n 걸음 동안 살아 있으면 W 는 n·δ 이상 줄었다. -/
theorem drop_accum (W : Nat → Nat) (alive : Nat → Prop) (δ : Nat)
    (drop : ∀ t, alive t → W (t+1) + δ ≤ W t) :
    ∀ n, (∀ t, t < n → alive t) → W n + n * δ ≤ W 0 := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro h
    have h1 := ih (fun t ht => h t (by omega))
    have h2 := drop n (h n (by omega))
    rw [Nat.succ_mul]
    omega

/-- 날카로운 꼴 : 어떤 시각 T 에서 T·δ ≤ W 0 이고 죽어 있다. -/
theorem finite_extinction_sharp (W : Nat → Nat) (alive : Nat → Prop) (δ : Nat)
    (hδ : 1 ≤ δ) (drop : ∀ t, alive t → W (t+1) + δ ≤ W t) :
    ∃ T, T * δ ≤ W 0 ∧ ¬ alive T := by
  apply Classical.byContradiction
  intro hne
  have hall : ∀ T, T * δ ≤ W 0 → alive T := by
    intro T hT
    apply Classical.byContradiction
    intro hna
    exact hne ⟨T, hT, hna⟩
  -- 모든 시각에서 살아 있음
  have hpre : ∀ n, ∀ t, t < n → alive t := by
    intro n
    induction n with
    | zero => intro t ht; omega
    | succ n ih =>
      intro t ht
      by_cases htn : t < n
      · exact ih t htn
      · have hteq : t = n := by omega
        subst hteq
        have := drop_accum W alive δ drop t ih
        exact hall t (by omega)
  have key := drop_accum W alive δ drop (W 0 + 1) (hpre (W 0 + 1))
  have hm : (W 0 + 1) * 1 ≤ (W 0 + 1) * δ := Nat.mul_le_mul_left (W 0 + 1) hδ
  rw [Nat.mul_one] at hm
  omega

/-- 소멸 시각 T ≤ W 0 / δ. -/
theorem finite_extinction_div (W : Nat → Nat) (alive : Nat → Prop) (δ : Nat)
    (hδ : 1 ≤ δ) (drop : ∀ t, alive t → W (t+1) + δ ≤ W t) :
    ∃ T, T ≤ W 0 / δ ∧ ¬ alive T := by
  obtain ⟨T, hT, hd⟩ := finite_extinction_sharp W alive δ hδ drop
  exact ⟨T, (Nat.le_div_iff_mul_le (by omega)).mpr hT, hd⟩

/-- 깔끔한 꼴 : 소멸 시각 T ≤ W 0. -/
theorem finite_extinction (W : Nat → Nat) (alive : Nat → Prop) (δ : Nat)
    (hδ : 1 ≤ δ) (drop : ∀ t, alive t → W (t+1) + δ ≤ W t) :
    ∃ T, T ≤ W 0 ∧ ¬ alive T := by
  obtain ⟨T, hT, hd⟩ := finite_extinction_sharp W alive δ hδ drop
  have hm : T * 1 ≤ T * δ := Nat.mul_le_mul_left T hδ
  rw [Nat.mul_one] at hm
  exact ⟨T, by omega, hd⟩

/-- 한 번 죽으면 계속 죽어 있다. -/
theorem dead_stays_dead (alive : Nat → Prop)
    (stay : ∀ t, ¬ alive t → ¬ alive (t+1)) (T : Nat) (hT : ¬ alive T) :
    ∀ t, T ≤ t → ¬ alive t := by
  intro t ht
  induction t with
  | zero =>
    have : T = 0 := by omega
    subst this; exact hT
  | succ t ih =>
    by_cases h : T ≤ t
    · exact stay t (ih h)
    · have : T = t + 1 := by omega
      subst this; exact hT

/-- 유한 소멸 + 한 번 죽으면 계속 : W 0 이후 모든 시각에서 죽어 있다. -/
theorem extinct_forever (W : Nat → Nat) (alive : Nat → Prop) (δ : Nat)
    (hδ : 1 ≤ δ) (drop : ∀ t, alive t → W (t+1) + δ ≤ W t)
    (stay : ∀ t, ¬ alive t → ¬ alive (t+1)) :
    ∀ t, W 0 ≤ t → ¬ alive t := by
  intro t ht
  obtain ⟨T, hT, hd⟩ := finite_extinction W alive δ hδ drop
  exact dead_stays_dead alive stay T hd t (by omega)

/-! ## 2. 수술 -/

/-- 처음 n 걸음 가운데 p 가 참인 걸음의 수. -/
def cnt (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n+1 => cnt p n + (if p n then 1 else 0)

theorem cnt_le (p : Nat → Bool) : ∀ n, cnt p n ≤ n := by
  intro n
  induction n with
  | zero => simp [cnt]
  | succ n ih => cases h : p n <;> simp [cnt, h] <;> omega

/-- 수술 걸음 수 + 보통 걸음 수 = n. -/
theorem cnt_split (p : Nat → Bool) :
    ∀ n, cnt p n + cnt (fun t => !p t) n = n := by
  intro n
  induction n with
  | zero => simp [cnt]
  | succ n ih => cases h : p n <;> simp [cnt, h] <;> omega

/-- 수술마다 V 를 ε 이상 쓰고 V 는 늘지 않으면 : (수술 수)·ε + V n ≤ V 0. -/
theorem surgery_accum (V : Nat → Nat) (surg : Nat → Bool) (ε : Nat)
    (hVmono : ∀ t, V (t+1) ≤ V t)
    (hVcost : ∀ t, surg t = true → V (t+1) + ε ≤ V t) :
    ∀ n, cnt surg n * ε + V n ≤ V 0 := by
  intro n
  induction n with
  | zero => simp [cnt]
  | succ n ih =>
    cases h : surg n
    · have := hVmono n
      simp [cnt, h]; omega
    · have := hVcost n h
      simp [cnt, h]; rw [Nat.succ_mul]; omega

/-- 수술 횟수 ≤ V 0 / ε (어느 시각까지 세어도). -/
theorem finite_surgeries (V : Nat → Nat) (surg : Nat → Bool) (ε : Nat) (hε : 1 ≤ ε)
    (hVmono : ∀ t, V (t+1) ≤ V t)
    (hVcost : ∀ t, surg t = true → V (t+1) + ε ≤ V t) :
    ∀ n, cnt surg n ≤ V 0 / ε := by
  intro n
  have := surgery_accum V surg ε hVmono hVcost n
  exact (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)

/-- 수술이 섞인 흐름의 누적 : 살아 있는 동안
    (보통 걸음 수)·δ + W n ≤ W 0 · (수술 걸음 수)·ε + V n ≤ V 0. -/
theorem mixed_accum (W V : Nat → Nat) (alive : Nat → Prop) (surg : Nat → Bool) (δ ε : Nat)
    (hreg : ∀ t, alive t → surg t = false → W (t+1) + δ ≤ W t ∧ V (t+1) ≤ V t)
    (hsurg : ∀ t, alive t → surg t = true → W (t+1) ≤ W t ∧ V (t+1) + ε ≤ V t) :
    ∀ n, (∀ t, t < n → alive t) →
      cnt (fun t => !surg t) n * δ + W n ≤ W 0 ∧ cnt surg n * ε + V n ≤ V 0 := by
  intro n
  induction n with
  | zero => intro _; simp [cnt]
  | succ n ih =>
    intro hal
    have ⟨i1, i2⟩ := ih (fun t ht => hal t (by omega))
    have an := hal n (by omega)
    cases h : surg n
    · have ⟨a, b⟩ := hreg n an h
      simp [cnt, h]
      rw [Nat.succ_mul]
      omega
    · have ⟨a, b⟩ := hsurg n an h
      simp [cnt, h]
      rw [Nat.succ_mul]
      omega

/-- 수술이 있는 유한 소멸 : 소멸 시각 T ≤ W 0 / δ + V 0 / ε. -/
theorem extinction_with_surgery (W V : Nat → Nat) (alive : Nat → Prop) (surg : Nat → Bool)
    (δ ε : Nat) (hδ : 1 ≤ δ) (hε : 1 ≤ ε)
    (hreg : ∀ t, alive t → surg t = false → W (t+1) + δ ≤ W t ∧ V (t+1) ≤ V t)
    (hsurg : ∀ t, alive t → surg t = true → W (t+1) ≤ W t ∧ V (t+1) + ε ≤ V t) :
    ∃ T, T ≤ W 0 / δ + V 0 / ε ∧ ¬ alive T := by
  apply Classical.byContradiction
  intro hne
  have hall : ∀ T, T ≤ W 0 / δ + V 0 / ε → alive T := by
    intro T hT
    apply Classical.byContradiction
    intro hna
    exact hne ⟨T, hT, hna⟩
  let B := W 0 / δ + V 0 / ε
  have hpre : ∀ t, t < B + 1 → alive t := fun t ht => hall t (by omega)
  have ⟨i1, i2⟩ := mixed_accum W V alive surg δ ε hreg hsurg (B + 1) hpre
  have r : cnt (fun t => !surg t) (B + 1) ≤ W 0 / δ :=
    (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have s : cnt surg (B + 1) ≤ V 0 / ε :=
    (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have sp := cnt_split surg (B + 1)
  omega

end Template

namespace RHSlot

/-! ## 3. 리만 가설 자리 (드 브라윈–뉴먼 꼴 · 조건부) -/

/-- 뒤로 가는 단조성이 있으면 0..T0 의 모든 시각에서 nonreal k ≤ nonreal T0. -/
theorem back_chain (T0 : Nat) (nonreal : Nat → Nat)
    (H_back : ∀ k, k < T0 → nonreal k ≤ nonreal (k+1)) :
    ∀ d k, k + d = T0 → nonreal k ≤ nonreal T0 := by
  intro d
  induction d with
  | zero => intro k hk; simp at hk; subst hk; exact Nat.le_refl _
  | succ d ih =>
    intro k hk
    have h1 := H_back k (by omega)
    have h2 := ih (k+1) (by omega)
    omega

/-- 조건부 정리 : (H_end) 끝 시각에 실수 아닌 영점 없음 · (H_back) 비어 있는 단조량
    ⟹ 시각 0 에서 실수 아닌 영점 없음 (RH 의 자리). -/
theorem rh_slot (T0 : Nat) (nonreal : Nat → Nat)
    (H_end : nonreal T0 = 0)
    (H_back : ∀ k, k < T0 → nonreal k ≤ nonreal (k+1)) :
    nonreal 0 = 0 := by
  have := back_chain T0 nonreal H_back T0 0 (by omega)
  omega

/-- 반례 모델 : 시각 0 에 실수 아닌 영점 2 개, 그 뒤로는 0 개. -/
def counterModel (k : Nat) : Nat := if k = 0 then 2 else 0

/-- H_back 없이는 결론이 나오지 않는다 : 반례 모델은 T0 ≥ 1 에서 H_end 를 만족하지만
    nonreal 0 = 2 ≠ 0 이고 H_back 을 어긴다. -/
theorem slot_needs_monotone :
    (∀ T0, 1 ≤ T0 →
      counterModel T0 = 0 ∧ counterModel 0 ≠ 0 ∧
      ¬ (∀ k, k < T0 → counterModel k ≤ counterModel (k+1))) ∧
    ¬ (∀ (T0 : Nat) (nonreal : Nat → Nat), nonreal T0 = 0 → nonreal 0 = 0) := by
  constructor
  · intro T0 hT0
    refine ⟨?_, ?_, ?_⟩
    · simp [counterModel]; omega
    · simp [counterModel]
    · intro h
      have := h 0 (by omega)
      simp [counterModel] at this
  · intro h
    have := h 1 counterModel (by simp [counterModel])
    simp [counterModel] at this

/-- 앞으로 가는 단조성 (열 흐름이 실제로 주는 방향 : 실수 영점은 시간이 가도 실수로 남는다)
    nonreal (k+1) ≤ nonreal k 를 H_end 와 함께 가정해도 결론은 나오지 않는다. -/
theorem forward_monotone_insufficient :
    (∀ k, counterModel (k+1) ≤ counterModel k) ∧ counterModel 1 = 0 ∧ counterModel 0 ≠ 0 ∧
    ¬ (∀ (T0 : Nat) (nonreal : Nat → Nat),
        (∀ k, nonreal (k+1) ≤ nonreal k) → nonreal T0 = 0 → nonreal 0 = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k; simp [counterModel]
  · simp [counterModel]
  · simp [counterModel]
  · intro h
    have := h 1 counterModel (by intro k; simp [counterModel]) (by simp [counterModel])
    simp [counterModel] at this

end RHSlot

