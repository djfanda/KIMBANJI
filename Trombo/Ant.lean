/-
  랭턴의 개미 — 코어에서 출발한 두 법칙과 영원히 한 방향
  (린 4 v4.34.0 코어 · Mathlib 없음 · import 없음)

  두 법칙 : 흰 칸이면 검게 칠하고 오른쪽으로 90° 돌아 한 칸, 검은 칸이면 희게 칠하고 왼쪽으로 90° 돌아 한 칸.
  칠하기는 F₂ 의 더하기(뒤집기), 돌기는 방향 곱하기 ∓i — 부호는 칸의 색이 정한다.

  1. 모든 판 · 모든 걸음에서 : 걸음마다 x + y 의 홀짝이 바뀌고(바둑판의 두 색을 번갈아 밟음), 방향은 가로와 세로를
     번갈아 가며(같은 쪽으로 두 번 가지 않음), 한 걸음은 거꾸로 되돌릴 수 있다(가역).
  2. 코어에서 빈 판으로 시작하면 걸음 10,704 에 개미는 (−28, −4) 에서 남쪽을 보고, 검은 칸은 798 개다(커널 셈).
  3. 그 뒤로 영원히 : k 번째 104 걸음마다 개미는 정확히 (−2, −2) 를 간다 — 모든 k 에서 (귀납 · 창 국소성).
     고속도로가 남서쪽으로 끝없이 뻗는다.
  4. 껍질을 뚫고 영원히 : 걸음 0 … 9,975 의 자리는 모두 상자 [−19, 29] × [−22, 22] 안이고(그 최소 · 최대가 바로 이 상자),
     고속도로는 걸음 9,976 에 덩어리 안쪽 (−14, 10) 에서 시작해 껍질을 뚫고, 걸음 10,287 부터 영원히 상자 밖 — 남서쪽 한 방향.
  남은 것(□) : 아무 유한한 처음 판에서도 고속도로가 생기는가는 열린 물음이다. 모든 유한 판에서 궤적이 유계가 아님
  (부니모비치–트루베츠코이 1992)은 전언.
-/

namespace Trombo.Ant

/-! ## 0. 두 법칙 -/

/-- 방향 0 북 · 1 동 · 2 남 · 3 서 — 오른쪽 90° 는 +1, 왼쪽 90° 는 +3 (mod 4) -/
def dx : Nat → Int
  | 1 => 1
  | 3 => -1
  | _ => 0

def dy : Nat → Int
  | 0 => 1
  | 2 => -1
  | _ => 0

/-- 개미 : 자리 (x, y) · 방향 d · 판 g (true = 검은 칸) -/
structure Ant where
  x : Int
  y : Int
  d : Nat
  g : Int → Int → Bool

/-- 흰 칸이면 검게 · 오른쪽 90° · 한 칸, 검은 칸이면 희게 · 왼쪽 90° · 한 칸 -/
def step (a : Ant) : Ant :=
  let c := a.g a.x a.y
  let d' := if c then (a.d + 3) % 4 else (a.d + 1) % 4
  { x := a.x + dx d', y := a.y + dy d', d := d',
    g := fun u v => if u = a.x ∧ v = a.y then !c else a.g u v }

def run : Nat → Ant → Ant
  | 0, a => a
  | n + 1, a => run n (step a)

/-- 코어 (0, 0) 에서 북쪽을 보고 · 판은 모두 흰 칸 -/
def core : Ant := ⟨0, 0, 0, fun _ _ => false⟩

theorem rule_white (a : Ant) (h : a.g a.x a.y = false) :
    (step a).d = (a.d + 1) % 4 ∧ (step a).g a.x a.y = true ∧
    (step a).x = a.x + dx ((a.d + 1) % 4) ∧ (step a).y = a.y + dy ((a.d + 1) % 4) := by
  simp [step, h]

theorem rule_black (a : Ant) (h : a.g a.x a.y = true) :
    (step a).d = (a.d + 3) % 4 ∧ (step a).g a.x a.y = false ∧
    (step a).x = a.x + dx ((a.d + 3) % 4) ∧ (step a).y = a.y + dy ((a.d + 3) % 4) := by
  simp [step, h]

theorem run_add (m n : Nat) (a : Ant) : run (m + n) a = run n (run m a) := by
  induction m generalizing a with
  | zero => simp [run]
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 by omega]
    simp only [run]
    exact ih (step a)

/-! ## 1. 모든 판에서 — 홀짝 · 가로세로 번갈음 · 되돌림 -/

theorem dxdy (d : Nat) (h : d < 4) : dx d + dy d = 1 ∨ dx d + dy d = -1 := by
  rcases d with _ | _ | _ | _ | d
  · simp [dx, dy]
  · simp [dx, dy]
  · simp [dx, dy]
  · simp [dx, dy]
  · omega

theorem step_xy (a : Ant) : (step a).x + (step a).y = a.x + a.y + 1 ∨ (step a).x + (step a).y = a.x + a.y - 1 := by
  simp only [step]
  split
  · have := dxdy ((a.d + 3) % 4) (Nat.mod_lt _ (by decide)); omega
  · have := dxdy ((a.d + 1) % 4) (Nat.mod_lt _ (by decide)); omega

/-- 걸음마다 x + y 의 홀짝이 바뀐다 — n 걸음 뒤 x + y ≡ (처음) + n (mod 2) : 바둑판의 두 색을 번갈아 밟는다 -/
theorem run_parity (n : Nat) (a : Ant) : ∃ k : Int, (run n a).x + (run n a).y = a.x + a.y + n - 2 * k := by
  induction n generalizing a with
  | zero => exact ⟨0, by simp [run]⟩
  | succ n ih =>
    obtain ⟨k, hk⟩ := ih (step a)
    simp only [run]
    rcases step_xy a with h | h
    · exact ⟨k, by rw [hk, h]; push_cast; omega⟩
    · exact ⟨k + 1, by rw [hk, h]; push_cast; omega⟩

/-- 방향의 홀짝도 걸음마다 바뀐다 — 가로와 세로를 번갈아 간다(같은 쪽으로 두 번 가지 않는다) -/
theorem run_turns (n : Nat) (a : Ant) : (run n a).d % 2 = (a.d + n) % 2 := by
  induction n generalizing a with
  | zero => simp [run]
  | succ n ih =>
    simp only [run]
    rw [ih (step a)]
    simp only [step]
    split <;> omega

/-- 한 걸음 되돌리기 -/
def unstep (b : Ant) : Ant :=
  let px := b.x - dx b.d
  let py := b.y - dy b.d
  let c := !(b.g px py)
  { x := px, y := py, d := if c then (b.d + 1) % 4 else (b.d + 3) % 4,
    g := fun u v => if u = px ∧ v = py then c else b.g u v }

theorem Ant.ext' {a b : Ant} (h1 : a.x = b.x) (h2 : a.y = b.y) (h3 : a.d = b.d) (h4 : a.g = b.g) : a = b := by
  cases a; cases b; simp_all

/-- 되돌림(가역) : 방향이 0 … 3 이면 unstep (step a) = a -/
theorem unstep_step (a : Ant) (h : a.d < 4) : unstep (step a) = a := by
  obtain ⟨x, y, d, g⟩ := a
  simp only at h
  have hx : (step ⟨x, y, d, g⟩).x - dx (step ⟨x, y, d, g⟩).d = x := by simp [step]
  have hy : (step ⟨x, y, d, g⟩).y - dy (step ⟨x, y, d, g⟩).d = y := by simp [step]
  have hc : (step ⟨x, y, d, g⟩).g x y = !g x y := by simp [step]
  apply Ant.ext'
  · simp only [unstep]; exact hx
  · simp only [unstep]; exact hy
  · simp only [unstep]; rw [hx, hy, hc]
    cases hg : g x y <;> simp [step, hg] <;> omega
  · simp only [unstep]; rw [hx, hy, hc]
    funext u v
    by_cases huv : u = x ∧ v = y
    · obtain ⟨rfl, rfl⟩ := huv; simp
    · simp [huv, step]


/-! ## 2. 판을 비트로 — 커널이 빠르게 세는 꼴과 두 꼴을 잇는 다리 -/

def inBox (u v : Int) : Bool := decide (-80 ≤ u ∧ u < 48 ∧ -64 ≤ v ∧ v < 64)
def idx (u v : Int) : Nat := ((v + 64) * 128 + (u + 80)).toNat

def bstep : Int × Int × Nat × Nat → Int × Int × Nat × Nat
  | (x, y, d, G) =>
    let i := idx x y
    let d' := if G.testBit i then (d + 3) % 4 else (d + 1) % 4
    (x + dx d', y + dy d', d', G ^^^ 2 ^ i)

def brun : Nat → Int × Int × Nat × Nat → Option (Int × Int × Nat × Nat)
  | 0, s => some s
  | n + 1, (x, y, d, G) =>
    if inBox x y then
      match bstep (x, y, d, G) with
      | (x', y', d', G') => brun n (x', y', d', G')
    else none

def decode : Int × Int × Nat × Nat → Ant
  | (x, y, d, G) => ⟨x, y, d, fun u v => inBox u v && G.testBit (idx u v)⟩

theorem idx_inj (u v u' v' : Int) (h : inBox u v = true) (h' : inBox u' v' = true)
    (e : idx u v = idx u' v') : u = u' ∧ v = v' := by
  simp only [inBox, idx, decide_eq_true_eq] at h h' e; omega

theorem decode_bstep (x y : Int) (d G : Nat) (h : inBox x y = true) :
    decode (bstep (x, y, d, G)) = step (decode (x, y, d, G)) := by
  apply Ant.ext'
  · simp [bstep, decode, step, h]
  · simp [bstep, decode, step, h]
  · simp [bstep, decode, step, h]
  · funext u v
    simp only [bstep, decode, step, h, Bool.true_and, Nat.testBit_xor, Nat.testBit_two_pow]
    by_cases huv : u = x ∧ v = y
    · obtain ⟨rfl, rfl⟩ := huv; simp [h]
    · simp only [huv]
      by_cases hb : inBox u v = true
      · have hne : ¬ (idx x y = idx u v) := fun e => huv (by have := idx_inj x y u v h hb e; omega)
        simp [hb, hne]
      · simp [hb]

theorem brun_decode : ∀ (n : Nat) (s s' : Int × Int × Nat × Nat), brun n s = some s' → decode s' = run n (decode s)
  | 0, s, s', h => by simp [brun] at h; subst h; rfl
  | n + 1, (x, y, d, G), s', h => by
    simp only [brun] at h
    split at h
    · rename_i hb
      have h' : brun n (bstep (x, y, d, G)) = some s' := h
      rw [brun_decode n _ _ h']
      simp only [run]
      rw [decode_bstep x y d G hb]
    · simp at h

theorem core_decode : decode (0, 0, 0, 0) = core := by
  apply Ant.ext' <;> simp [decode, core]

/-! ## 3. 걸음 10,704 — 커널이 처음부터 센 판 -/

/-- 걸음 10,704 의 개미 둘레(가로세로 21 칸)의 무늬 : 행 Δy = −10 … 10, 비트 Δx + 10 -/
def rows : List Nat := [0, 0, 0, 0, 1536, 3840, 5760, 13440, 21760, 51456, 84864, 205696, 342272, 822784,
  1369088, 1193984, 1282048, 581632, 933888, 229376, 1638400]

def winOK (G : Nat) : Bool :=
  (List.range 21).all fun j => (List.range 21).all fun i =>
    G.testBit (idx (-28 + (i : Int) - 10) (-4 + (j : Int) - 10)) == (rows.getD j 0).testBit i

/-- 창 밖의 검은 칸은 모두 x > −20 이거나 y > 4 — 남서쪽 앞길은 비어 있다 -/
def condC (G : Nat) : Bool :=
  (List.range 128).all fun j => (List.range 128).all fun i =>
    !(G.testBit (idx ((i : Int) - 80) ((j : Int) - 64))) ||
    decide (-38 ≤ (i : Int) - 80 ∧ (i : Int) - 80 ≤ -18 ∧ -14 ≤ (j : Int) - 64 ∧ (j : Int) - 64 ≤ 6) ||
    decide ((i : Int) - 80 > -20) || decide ((j : Int) - 64 > 4)

def t1Check : Bool :=
  match brun 10704 (0, 0, 0, 0) with
  | some (x, y, d, G) => x == -28 && y == -4 && d == 2 && winOK G && condC G
  | none => false

theorem t1_ok : t1Check = true := by decide +kernel

theorem t1_state : ∃ G1, brun 10704 (0, 0, 0, 0) = some (-28, -4, 2, G1) ∧ winOK G1 = true ∧ condC G1 = true := by
  have h := t1_ok
  unfold t1Check at h
  split at h
  · rename_i x y d G heq
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨hx, hy⟩, hd⟩, hw⟩, hc⟩ := h
    subst hx hy hd
    exact ⟨G, heq, hw, hc⟩
  · simp at h


/-! ## 4. 한 블록 — 104 걸음의 국소 셈 -/

def inW0 (u v : Int) : Bool := decide (-10 ≤ u ∧ u ≤ 10 ∧ -10 ≤ v ∧ v ≤ 10)

/-- 개미 둘레 무늬 P (개미 자리를 (0, 0) 으로) -/
def Pfun (u v : Int) : Bool := inW0 u v && (rows.getD (v + 10).toNat 0).testBit (u + 10).toNat

def blk : Ant := ⟨0, 0, 2, Pfun⟩

def stays : Nat → Ant → Bool
  | 0, _ => true
  | n + 1, a => inW0 a.x a.y && stays n (step a)

def blkCheck : Bool :=
  stays 104 blk && (run 104 blk).x == -2 && (run 104 blk).y == -2 && (run 104 blk).d == 2 &&
  ((List.range 19).all fun j => (List.range 19).all fun i =>
     (run 104 blk).g ((i : Int) - 10) ((j : Int) - 10) == Pfun ((i : Int) - 8) ((j : Int) - 8)) &&
  ((List.range 21).all fun j => (List.range 21).all fun i =>
     !(decide ((i : Int) - 10 ≤ -9 ∨ (j : Int) - 10 ≤ -9)) || !(Pfun ((i : Int) - 10) ((j : Int) - 10)))

theorem blk_ok : blkCheck = true := by decide +kernel

theorem blk_facts :
    stays 104 blk = true ∧ (run 104 blk).x = -2 ∧ (run 104 blk).y = -2 ∧ (run 104 blk).d = 2 ∧
    (∀ u v : Int, -10 ≤ u → u ≤ 8 → -10 ≤ v → v ≤ 8 → (run 104 blk).g u v = Pfun (u + 2) (v + 2)) ∧
    (∀ u v : Int, (u ≤ -9 ∨ v ≤ -9) → Pfun u v = false) := by
  have h := blk_ok
  simp only [blkCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨hs, hx⟩, hy⟩, hd⟩, hov⟩, hsw⟩ := h
  refine ⟨hs, hx, hy, hd, ?_, ?_⟩
  · intro u v hu1 hu2 hv1 hv2
    have := hov (v + 10).toNat (by omega) (u + 10).toNat (by omega)
    have e1 : ((u + 10).toNat : Int) - 10 = u := by omega
    have e2 : ((v + 10).toNat : Int) - 10 = v := by omega
    have e3 : ((u + 10).toNat : Int) - 8 = u + 2 := by omega
    have e4 : ((v + 10).toNat : Int) - 8 = v + 2 := by omega
    rw [e1, e2, e3, e4] at this
    exact this
  · intro u v huv
    by_cases hin : inW0 u v = true
    · simp only [inW0, decide_eq_true_eq] at hin
      have := hsw (v + 10).toNat (by omega) (u + 10).toNat (by omega)
      have e1 : ((u + 10).toNat : Int) - 10 = u := by omega
      have e2 : ((v + 10).toNat : Int) - 10 = v := by omega
      rw [e1, e2] at this
      simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at this
      rcases this with h1 | h1
      · exact absurd huv h1
      · exact h1
    · simp only [Pfun, Bool.and_eq_false_iff]
      left; simpa using hin

/-! ## 5. 옮김과 국소성 — 창 안만 읽고 창 안만 바꾼다 -/

def shift (c : Int × Int) (a : Ant) : Ant := ⟨a.x + c.1, a.y + c.2, a.d, fun u v => a.g (u - c.1) (v - c.2)⟩

theorem step_shift (c : Int × Int) (a : Ant) : step (shift c a) = shift c (step a) := by
  apply Ant.ext'
  · simp [step, shift]; omega
  · simp [step, shift]; omega
  · simp [step, shift]
  · funext u v
    simp only [step, shift, Int.add_sub_cancel]
    by_cases huv : u - c.1 = a.x ∧ v - c.2 = a.y
    · have h2 : u = a.x + c.1 ∧ v = a.y + c.2 := by omega
      simp [h2]
    · have h2 : ¬ (u = a.x + c.1 ∧ v = a.y + c.2) := by omega
      simp [huv, h2]

theorem run_shift (n : Nat) (c : Int × Int) (a : Ant) : run n (shift c a) = shift c (run n a) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp only [run]; rw [step_shift, ih]

def agreeW (g h : Int → Int → Bool) : Prop := ∀ u v, inW0 u v = true → g u v = h u v

theorem run_agree : ∀ (n : Nat) (a b : Ant), a.x = b.x → a.y = b.y → a.d = b.d → agreeW a.g b.g →
    stays n b = true →
    (run n a).x = (run n b).x ∧ (run n a).y = (run n b).y ∧ (run n a).d = (run n b).d ∧
    agreeW (run n a).g (run n b).g ∧ (∀ u v, inW0 u v = false → (run n a).g u v = a.g u v)
  | 0, a, b, hx, hy, hd, hg, _ => ⟨hx, hy, hd, hg, fun _ _ _ => rfl⟩
  | n + 1, a, b, hx, hy, hd, hg, hs => by
    simp only [stays, Bool.and_eq_true] at hs
    obtain ⟨hin, hs⟩ := hs
    have hc : a.g a.x a.y = b.g b.x b.y := by rw [hx, hy]; exact hg _ _ hin
    have h1 : (step a).x = (step b).x := by simp only [step]; rw [hc, hx, hd]
    have h2 : (step a).y = (step b).y := by simp only [step]; rw [hc, hy, hd]
    have h3 : (step a).d = (step b).d := by simp only [step]; rw [hc, hd]
    have h4 : agreeW (step a).g (step b).g := by
      intro u v huv
      simp only [step]
      rw [hc, hx, hy]
      split
      · rfl
      · exact hg u v huv
    have h5 : ∀ u v, inW0 u v = false → (step a).g u v = a.g u v := by
      intro u v huv
      simp only [step]
      have : ¬ (u = a.x ∧ v = a.y) := by
        rintro ⟨rfl, rfl⟩
        rw [hx, hy] at huv
        rw [huv] at hin
        exact Bool.false_ne_true hin
      simp [this]
    obtain ⟨r1, r2, r3, r4, r5⟩ := run_agree n (step a) (step b) h1 h2 h3 h4 hs
    refine ⟨r1, r2, r3, r4, fun u v huv => ?_⟩
    simp only [run]
    rw [r5 u v huv, h5 u v huv]

theorem stays_le : ∀ (n m : Nat) (a : Ant), m ≤ n → stays n a = true → stays m a = true
  | _, 0, _, _, _ => rfl
  | 0, m + 1, _, h, _ => absurd h (by omega)
  | n + 1, m + 1, a, h, hs => by
    simp only [stays, Bool.and_eq_true] at hs ⊢
    exact ⟨hs.1, stays_le n m (step a) (by omega) hs.2⟩

/-! ## 6. 영원히 남서쪽 — 모든 k 에서 -/

/-- k 번째 블록의 불변식 : 자리 (−28 − 2k, −4 − 2k) · 남쪽 · 둘레 무늬 P · 남서쪽 앞길은 처음 판 그대로 -/
def Inv (g1 : Int → Int → Bool) (k : Nat) (a : Ant) : Prop :=
  a.x = -28 - 2 * (k : Int) ∧ a.y = -4 - 2 * (k : Int) ∧ a.d = 2 ∧
  (∀ u v, inW0 u v = true → a.g (u + a.x) (v + a.y) = Pfun u v) ∧
  (∀ u v, (u < -38 - 2 * (k : Int) ∨ v < -14 - 2 * (k : Int)) → a.g u v = g1 u v)

theorem rel_shift (a : Ant) : shift (a.x, a.y) ⟨0, 0, a.d, fun u v => a.g (u + a.x) (v + a.y)⟩ = a := by
  apply Ant.ext' <;> simp [shift]

theorem inv_step (g1 : Int → Int → Bool)
    (hw : ∀ u v, u ≤ -20 → v ≤ 4 → (u < -38 ∨ v < -14) → g1 u v = false)
    (k : Nat) (a : Ant) (h : Inv g1 k a) : Inv g1 (k + 1) (run 104 a) := by
  obtain ⟨hx, hy, hd, hP, hS⟩ := h
  obtain ⟨bs, bx, byy, bd, bov, bsw⟩ := blk_facts
  let ar : Ant := ⟨0, 0, a.d, fun u v => a.g (u + a.x) (v + a.y)⟩
  have hagree : agreeW ar.g blk.g := fun u v huv => hP u v huv
  obtain ⟨r1, r2, r3, r4, r5⟩ := run_agree 104 ar blk rfl rfl (by simp [ar, blk, hd]) hagree bs
  have hb : run 104 a = shift (a.x, a.y) (run 104 ar) := by
    conv => lhs; rw [← rel_shift a]
    exact run_shift 104 (a.x, a.y) ar
  rw [hb]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [shift]; rw [r1, bx, hx]; push_cast; omega
  · simp only [shift]; rw [r2, byy, hy]; push_cast; omega
  · simp only [shift]; rw [r3, bd]
  · intro u v huv
    simp only [shift, r1, r2, bx, byy]
    have e1 : u + (-2 + a.x) - a.x = u - 2 := by omega
    have e2 : v + (-2 + a.y) - a.y = v - 2 := by omega
    rw [e1, e2]
    simp only [inW0, decide_eq_true_eq] at huv
    by_cases hin : inW0 (u - 2) (v - 2) = true
    · rw [r4 _ _ hin]
      simp only [inW0, decide_eq_true_eq] at hin
      have hb2 := bov (u - 2) (v - 2) (by omega) (by omega) (by omega) (by omega)
      have e3 : u - 2 + 2 = u := by omega
      have e4 : v - 2 + 2 = v := by omega
      rw [e3, e4] at hb2
      exact hb2
    · have hin' : inW0 (u - 2) (v - 2) = false := by simpa using hin
      rw [r5 _ _ hin']
      simp only [ar]
      have hPf : Pfun u v = false := by
        simp only [inW0, decide_eq_true_eq] at hin
        exact bsw u v (by omega)
      rw [hPf]
      simp only [inW0, decide_eq_true_eq] at hin
      rw [hS _ _ (by omega)]
      exact hw _ _ (by omega) (by omega) (by omega)
  · intro u v huv
    simp only [shift]
    have hout : inW0 (u - a.x) (v - a.y) = false := by
      simp only [inW0, decide_eq_false_iff_not]; omega
    rw [r5 _ _ hout]
    simp only [ar]
    have e1 : u - a.x + a.x = u := by omega
    have e2 : v - a.y + a.y = v := by omega
    rw [e1, e2]
    exact hS u v (by push_cast at huv; omega)

theorem white_of_condC (G : Nat) (hc : condC G = true) :
    ∀ u v, u ≤ -20 → v ≤ 4 → (u < -38 ∨ v < -14) → (decode (-28, -4, 2, G)).g u v = false := by
  intro u v hu hv huv
  simp only [decode, Bool.and_eq_false_iff]
  by_cases hb : inBox u v = true
  · right
    simp only [inBox, decide_eq_true_eq] at hb
    simp only [condC, List.all_eq_true, List.mem_range] at hc
    have := hc (v + 64).toNat (by omega) (u + 80).toNat (by omega)
    have e1 : ((u + 80).toNat : Int) - 80 = u := by omega
    have e2 : ((v + 64).toNat : Int) - 64 = v := by omega
    rw [e1, e2] at this
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at this
    rcases this with ((h1 | h1) | h1) | h1
    · exact h1
    · omega
    · omega
    · omega
  · left; simpa using hb

theorem inv_base (G : Nat) (hw : winOK G = true) : Inv (decode (-28, -4, 2, G)).g 0 (decode (-28, -4, 2, G)) := by
  refine ⟨rfl, rfl, rfl, ?_, fun _ _ _ => rfl⟩
  intro u v huv
  simp only [inW0, decide_eq_true_eq] at huv
  simp only [winOK, List.all_eq_true, List.mem_range, beq_iff_eq] at hw
  have := hw (v + 10).toNat (by omega) (u + 10).toNat (by omega)
  have e1 : -28 + ((u + 10).toNat : Int) - 10 = u + -28 := by omega
  have e2 : -4 + ((v + 10).toNat : Int) - 10 = v + -4 := by omega
  rw [e1, e2] at this
  simp only [decode, Pfun]
  have hb : inBox (u + -28) (v + -4) = true := by simp only [inBox, decide_eq_true_eq]; omega
  have hi : inW0 u v = true := by simp only [inW0, decide_eq_true_eq]; omega
  rw [hb, hi, Bool.true_and, Bool.true_and, this]

theorem inv_all : ∃ g1, ∀ k : Nat, Inv g1 k (run (10704 + 104 * k) core) := by
  obtain ⟨G, hrun, hwin, hcc⟩ := t1_state
  have hbase : run 10704 core = decode (-28, -4, 2, G) := by
    rw [← core_decode]; exact (brun_decode 10704 _ _ hrun).symm
  have hw := white_of_condC G hcc
  refine ⟨(decode (-28, -4, 2, G)).g, fun k => ?_⟩
  induction k with
  | zero => rw [Nat.mul_zero, Nat.add_zero, hbase]; exact inv_base G hwin
  | succ k ih =>
    rw [show 10704 + 104 * (k + 1) = (10704 + 104 * k) + 104 by omega, run_add]
    exact inv_step _ hw k _ ih

/-- 고속도로 : 걸음 10,704 + 104k 에서 개미는 (−28 − 2k, −4 − 2k) 에 있고 남쪽을 본다 — 모든 k 에서 -/
theorem highway_forever (k : Nat) :
    (run (10704 + 104 * k) core).x = -28 - 2 * (k : Int) ∧
    (run (10704 + 104 * k) core).y = -4 - 2 * (k : Int) ∧ (run (10704 + 104 * k) core).d = 2 := by
  obtain ⟨g1, key⟩ := inv_all
  obtain ⟨hx, hy, hd, _, _⟩ := key k
  exact ⟨hx, hy, hd⟩

/-- 블록 안의 자리 : 불변식을 만족하는 개미의 j 걸음(j ≤ 104) 자리 = 블록 첫 자리 + 국소 셈의 자리 -/
theorem inv_pos (g1 : Int → Int → Bool) (k : Nat) (a : Ant) (h : Inv g1 k a) (j : Nat) (hj : j ≤ 104) :
    (run j a).x = a.x + (run j blk).x ∧ (run j a).y = a.y + (run j blk).y := by
  obtain ⟨hx, hy, hd, hP, hS⟩ := h
  obtain ⟨bs, _, _, _, _, _⟩ := blk_facts
  let ar : Ant := ⟨0, 0, a.d, fun u v => a.g (u + a.x) (v + a.y)⟩
  have hagree : agreeW ar.g blk.g := fun u v huv => hP u v huv
  obtain ⟨r1, r2, _, _, _⟩ := run_agree j ar blk rfl rfl (by simp [ar, blk, hd]) hagree (stays_le 104 j blk hj bs)
  have hb : run j a = shift (a.x, a.y) (run j ar) := by
    conv => lhs; rw [← rel_shift a]
    exact run_shift j (a.x, a.y) ar
  rw [hb]
  simp only [shift]
  rw [r1, r2]
  constructor <;> omega

theorem stays_pos : ∀ (n : Nat) (a : Ant), stays n a = true → ∀ j < n, inW0 (run j a).x (run j a).y = true
  | 0, _, _, j, hj => absurd hj (by omega)
  | n + 1, a, hs, j, hj => by
    simp only [stays, Bool.and_eq_true] at hs
    cases j with
    | zero => exact hs.1
    | succ j => simp only [run]; exact stays_pos n (step a) hs.2 j (by omega)

/-- 걸음 10,704 부터 영원히 : 104 걸음 뒤의 자리 = 지금 자리 + (−2, −2) -/
theorem drift_forever (t : Nat) (ht : 10704 ≤ t) :
    (run (t + 104) core).x = (run t core).x - 2 ∧ (run (t + 104) core).y = (run t core).y - 2 := by
  obtain ⟨g1, key⟩ := inv_all
  have ht' : t = 10704 + 104 * ((t - 10704) / 104) + (t - 10704) % 104 := by omega
  have hj : (t - 10704) % 104 < 104 := Nat.mod_lt _ (by decide)
  generalize (t - 10704) / 104 = k at ht'
  generalize (t - 10704) % 104 = j at ht' hj
  have e1 : run t core = run j (run (10704 + 104 * k) core) := by
    rw [← run_add, ← ht']
  have e2 : run (t + 104) core = run j (run (10704 + 104 * (k + 1)) core) := by
    rw [← run_add]; congr 1; omega
  obtain ⟨ax, ay, _, _, _⟩ := key k
  obtain ⟨bx, by2, _, _, _⟩ := key (k + 1)
  obtain ⟨p1, p2⟩ := inv_pos g1 k _ (key k) j (by omega)
  obtain ⟨q1, q2⟩ := inv_pos g1 (k + 1) _ (key (k + 1)) j (by omega)
  rw [e1, e2, p1, p2, q1, q2, ax, ay, bx, by2]
  push_cast
  constructor <;> omega

/-! ## 7. 임계점 — 걸음 9,976 부터 영원히, 9,975 에서는 아님 · 코어에 마지막으로 선 걸음 8,068 -/

/-- 상태 s 부터 n 걸음까지의 자리 목록(n + 1 개) — 상자를 벗어나면 none -/
def bpos : Nat → Int × Int × Nat × Nat → Option (List (Int × Int))
  | 0, (x, y, _, _) => some [(x, y)]
  | n + 1, (x, y, d, G) =>
    if inBox x y then (bpos n (bstep (x, y, d, G))).map (fun L => (x, y) :: L) else none

theorem bpos_spec : ∀ (n : Nat) (s : Int × Int × Nat × Nat) (L : List (Int × Int)), bpos n s = some L →
    ∀ j ≤ n, L.getD j (0, 0) = ((run j (decode s)).x, (run j (decode s)).y)
  | 0, (x, y, d, G), L, h, j, hj => by
    simp only [bpos, Option.some.injEq] at h
    subst h
    have : j = 0 := by omega
    subst this
    simp [run, decode]
  | n + 1, (x, y, d, G), L, h, j, hj => by
    simp only [bpos] at h
    split at h
    · rename_i hb
      cases hL : bpos n (bstep (x, y, d, G)) with
      | none => simp [hL] at h
      | some L' =>
        simp only [hL, Option.map_some, Option.some.injEq] at h
        subst h
        cases j with
        | zero => simp [run, decode]
        | succ j =>
          simp only [List.getD_cons_succ]
          rw [bpos_spec n _ L' hL j (by omega)]
          simp only [run]
          rw [decode_bstep x y d G hb]
    · simp at h

def critCheck : Bool :=
  match brun 9975 (0, 0, 0, 0) with
  | some s =>
    match bpos 833 s with
    | some L =>
      ((List.range 728).all fun j =>
        (L.getD (j + 1 + 104) (0, 0)).1 == (L.getD (j + 1) (0, 0)).1 - 2 &&
        (L.getD (j + 1 + 104) (0, 0)).2 == (L.getD (j + 1) (0, 0)).2 - 2) &&
      !((L.getD 104 (0, 0)).1 == (L.getD 0 (0, 0)).1 - 2 && (L.getD 104 (0, 0)).2 == (L.getD 0 (0, 0)).2 - 2)
    | none => false
  | none => false

theorem crit_ok : critCheck = true := by decide +kernel

/-- 임계점 : 걸음 9,976 부터는 영원히 104 걸음마다 (−2, −2), 걸음 9,975 에서는 그렇지 않다 -/
theorem critical_point :
    (∀ t, 9976 ≤ t → (run (t + 104) core).x = (run t core).x - 2 ∧ (run (t + 104) core).y = (run t core).y - 2) ∧
    ¬ ((run (9975 + 104) core).x = (run 9975 core).x - 2 ∧ (run (9975 + 104) core).y = (run 9975 core).y - 2) := by
  have h := crit_ok
  unfold critCheck at h
  split at h
  · rename_i s hs
    split at h
    · rename_i L hL
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_range, beq_iff_eq] at h
      obtain ⟨hall, hnot⟩ := h
      have hr : run 9975 core = decode s := by rw [← core_decode]; exact (brun_decode 9975 _ _ hs).symm
      have posAt : ∀ j ≤ 833, ((run (9975 + j) core).x, (run (9975 + j) core).y) = L.getD j (0, 0) := by
        intro j hj; rw [run_add, hr]; exact (bpos_spec 833 s L hL j hj).symm
      constructor
      · intro t ht
        by_cases hlt : t < 10704
        · have a1 := posAt (t - 9975) (by omega)
          have a2 := posAt (t - 9975 + 104) (by omega)
          have e1 : 9975 + (t - 9975) = t := by omega
          have e2 : 9975 + (t - 9975 + 104) = t + 104 := by omega
          rw [e1] at a1; rw [e2] at a2
          have c := hall (t - 9976) (by omega)
          have e3 : t - 9976 + 1 = t - 9975 := by omega
          rw [e3] at c
          rw [← a1, ← a2] at c
          exact ⟨c.1, c.2⟩
        · exact drift_forever t (by omega)
      · intro hc
        have a1 := posAt 0 (by omega)
        have a2 := posAt 104 (by omega)
        rw [Nat.add_zero] at a1
        rw [← a1, ← a2] at hnot
        simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hnot
        rcases hnot with h1 | h1
        · exact h1 hc.1
        · exact h1 hc.2
    · simp at h
  · simp at h

/-! ## 8. 껍질을 뚫고 한 방향으로 — 걸음 10,287 부터 영원히 덩어리 상자 밖

걸음 0 … 9,975 에 개미가 밟은 칸은 모두 상자 [−19, 29] × [−22, 22] 안에 있고, 그 자리들의 최솟값 · 최댓값이 정확히
이 상자다(커널 셈). 고속도로는 걸음 9,976 에 덩어리 안쪽 (−14, 10) 에서 시작한다(임계점 · 밟지 않은 칸까지 네 칸 · 셈).
개미는 걸음 10,182 의 (−17, 7) 에서 덩어리의 칸을 마지막으로 밟고 다음 걸음에 껍질을 뚫는다(셈). 걸음 10,286 에
마지막으로 상자 안 (−19, 5) 에 있다가 걸음 10,287 에 (−20, 5) 로 나간 뒤 다시 들어오지 않는다 — 남서쪽 한 방향. -/

/-- 덩어리 상자 -/
def inBlob (u v : Int) : Bool := decide (-19 ≤ u ∧ u ≤ 29 ∧ -22 ≤ v ∧ v ≤ 22)

/-- 상자 B = (x 최소, x 최대, y 최소, y 최대) 를 자리 (x, y) 로 넓힘 -/
def upd (B : Int × Int × Int × Int) (x y : Int) : Int × Int × Int × Int :=
  (min B.1 x, max B.2.1 x, min B.2.2.1 y, max B.2.2.2 y)

/-- 상자가 바른 꼴인지 (언제나 참 — 걸음마다 상자의 네 값을 셈해 두게 한다) -/
def okB (B : Int × Int × Int × Int) : Bool := decide (B.1 ≤ B.2.1 ∧ B.2.2.1 ≤ B.2.2.2)

/-- n 걸음 동안의 자리로 상자를 넓혀 감 (꼬리 되부름) -/
def bbox : Nat → Int × Int × Nat × Nat → Int × Int × Int × Int → Option (Int × Int × Int × Int)
  | 0, (x, y, _, _), B => some (upd B x y)
  | n + 1, (x, y, d, G), B =>
    if inBox x y && okB B then
      match bstep (x, y, d, G) with
      | (x', y', d', G') => bbox n (x', y', d', G') (upd B x y)
    else none

def within (B : Int × Int × Int × Int) (x y : Int) : Prop := B.1 ≤ x ∧ x ≤ B.2.1 ∧ B.2.2.1 ≤ y ∧ y ≤ B.2.2.2

def sub (B B' : Int × Int × Int × Int) : Prop := B'.1 ≤ B.1 ∧ B.2.1 ≤ B'.2.1 ∧ B'.2.2.1 ≤ B.2.2.1 ∧ B.2.2.2 ≤ B'.2.2.2

theorem upd_within (B : Int × Int × Int × Int) (x y : Int) : within (upd B x y) x y := by
  simp only [within, upd]; omega

theorem upd_sub (B : Int × Int × Int × Int) (x y : Int) : sub B (upd B x y) := by
  simp only [sub, upd]; omega

theorem bbox_spec : ∀ (n : Nat) (s : Int × Int × Nat × Nat) (B B' : Int × Int × Int × Int), bbox n s B = some B' →
    sub B B' ∧ ∀ j ≤ n, within B' (run j (decode s)).x (run j (decode s)).y
  | 0, (x, y, d, G), B, B', h => by
    simp only [bbox, Option.some.injEq] at h
    subst h
    refine ⟨upd_sub B x y, fun j hj => ?_⟩
    have : j = 0 := by omega
    subst this
    exact upd_within B x y
  | n + 1, (x, y, d, G), B, B', h => by
    simp only [bbox] at h
    split at h
    · rename_i hb0
      have hb : inBox x y = true := by simp only [Bool.and_eq_true] at hb0; exact hb0.1
      have h' : bbox n (bstep (x, y, d, G)) (upd B x y) = some B' := h
      obtain ⟨hs, hw⟩ := bbox_spec n _ _ _ h'
      have hs0 := upd_sub B x y
      have hw0 := upd_within B x y
      refine ⟨?_, fun j hj => ?_⟩
      · simp only [sub] at hs hs0 ⊢; omega
      · cases j with
        | zero =>
          simp only [run, decode]
          simp only [within, sub] at hs hw0 ⊢; omega
        | succ j =>
          have := hw j (by omega)
          rw [decode_bstep x y d G hb] at this
          simp only [run]
          exact this
    · simp at h

theorem bbox_ok : bbox 9975 (0, 0, 0, 0) (0, 0, 0, 0) = some (-19, 29, -22, 22) := by decide +kernel

/-- ★ 덩어리 상자 : 걸음 0 … 9,975 의 모든 자리가 [−19, 29] × [−22, 22] 안 (그 자리들의 최소 · 최대가 바로 이 상자) -/
theorem blob_box (t : Nat) (ht : t ≤ 9975) : inBlob (run t core).x (run t core).y = true := by
  obtain ⟨_, hw⟩ := bbox_spec 9975 _ _ _ bbox_ok
  have := hw t ht
  rw [core_decode] at this
  simp only [within] at this
  simp only [inBlob, decide_eq_true_eq]
  omega

def escCheck : Bool :=
  match brun 9975 (0, 0, 0, 0) with
  | some s =>
    match bpos 833 s with
    | some L =>
      ((List.range 522).all fun j => !inBlob (L.getD (j + 312) (0, 0)).1 (L.getD (j + 312) (0, 0)).2) &&
        inBlob (L.getD 311 (0, 0)).1 (L.getD 311 (0, 0)).2 &&
        L.getD 1 (0, 0) == (-14, 10) && L.getD 311 (0, 0) == (-19, 5) && L.getD 312 (0, 0) == (-20, 5)
    | none => false
  | none => false

theorem esc_ok : escCheck = true := by decide +kernel

/-- 걸음 10,808 부터 (k ≥ 1 블록) : x ≤ −20 -/
theorem tail_x (t : Nat) (ht : 10808 ≤ t) : (run t core).x ≤ -20 := by
  obtain ⟨g1, key⟩ := inv_all
  obtain ⟨bs, _, _, _, _, _⟩ := blk_facts
  have ht' : t = 10704 + 104 * ((t - 10704) / 104) + (t - 10704) % 104 := by omega
  have hj : (t - 10704) % 104 < 104 := Nat.mod_lt _ (by decide)
  have hk : 1 ≤ (t - 10704) / 104 := by omega
  generalize (t - 10704) / 104 = k at ht' hk
  generalize (t - 10704) % 104 = j at ht' hj
  have e1 : run t core = run j (run (10704 + 104 * k) core) := by
    rw [← run_add, ← ht']
  obtain ⟨ax, _, _, _, _⟩ := key k
  obtain ⟨p1, _⟩ := inv_pos g1 k _ (key k) j (by omega)
  have hw := stays_pos 104 blk bs j hj
  simp only [inW0, decide_eq_true_eq] at hw
  rw [e1, p1, ax]
  omega

/-- ★ 껍질을 뚫고 영원히 : 걸음 10,287 부터 개미는 덩어리 상자 밖에 있고 다시 들어오지 않는다 · 걸음 10,286 에는 아직 안 ·
    고속도로의 첫 자리 (걸음 9,976) 는 덩어리 안쪽의 (−14, 10) -/
theorem escape_forever :
    (∀ t, 10287 ≤ t → inBlob (run t core).x (run t core).y = false) ∧
    inBlob (run 10286 core).x (run 10286 core).y = true ∧
    ((run 9976 core).x = -14 ∧ (run 9976 core).y = 10) := by
  have h := esc_ok
  unfold escCheck at h
  split at h
  · rename_i s hs
    split at h
    · rename_i L hL
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_range, beq_iff_eq] at h
      obtain ⟨⟨⟨⟨hall, hin⟩, h1⟩, _⟩, _⟩ := h
      have hr : run 9975 core = decode s := by rw [← core_decode]; exact (brun_decode 9975 _ _ hs).symm
      have posAt : ∀ j ≤ 833, ((run (9975 + j) core).x, (run (9975 + j) core).y) = L.getD j (0, 0) := by
        intro j hj; rw [run_add, hr]; exact (bpos_spec 833 s L hL j hj).symm
      have posX : ∀ j ≤ 833, (run (9975 + j) core).x = (L.getD j (0, 0)).1 := fun j hj => congrArg Prod.fst (posAt j hj)
      have posY : ∀ j ≤ 833, (run (9975 + j) core).y = (L.getD j (0, 0)).2 := fun j hj => congrArg Prod.snd (posAt j hj)
      refine ⟨?_, ?_, ?_⟩
      · intro t ht
        by_cases hlt : t ≤ 10808
        · have a1 := posAt (t - 9975) (by omega)
          have e1 : 9975 + (t - 9975) = t := by omega
          rw [e1] at a1
          have c := hall (t - 10287) (by omega)
          have e3 : t - 10287 + 312 = t - 9975 := by omega
          rw [e3, ← a1] at c
          exact c
        · have := tail_x t (by omega)
          simp only [inBlob]
          apply decide_eq_false
          omega
      · have ex := posX 311 (by omega)
        have ey := posY 311 (by omega)
        rw [show (9975 + 311 : Nat) = 10286 from rfl] at ex ey
        rw [ex, ey]
        exact hin
      · have ex := posX 1 (by omega)
        have ey := posY 1 (by omega)
        rw [show (9975 + 1 : Nat) = 9976 from rfl] at ex ey
        rw [ex, ey, h1]
        exact ⟨rfl, rfl⟩
    · simp at h
  · simp at h

end Trombo.Ant


#print axioms Trombo.Ant.highway_forever
#print axioms Trombo.Ant.critical_point
#print axioms Trombo.Ant.escape_forever
#print axioms Trombo.Ant.blob_box
#print axioms Trombo.Ant.unstep_step
#print axioms Trombo.Ant.run_parity
