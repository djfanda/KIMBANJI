/-
동서 축 — 2 차원 Z₂ 격자 게이지 이론의 정확한 셈과 원환면의 베티 수 (린 4 코어 · 자연수 비트 셈)

원환면 위 Lx × Ly 격자 (꼭짓점 N = Lx·Ly · 고리 2N · 판 N). 고리마다 U = ±1 (비트 0 = +1, 1 = −1),
판의 값은 둘레 네 고리의 곱 (비트로는 XOR). 고리 배치 2^{2N} 가지를 모두 세어
  · 음의 판이 k 개인 배치 수 = 2^{N+1} · C(N, k)  (k 짝수),  0  (k 홀수)
임을 커널이 확인한다 (2 × 2 · 2 × 3 은 여기서, 3 × 3 의 2^18 가지는 GaugeZ2Big 에서 토막으로). 이것이 곧 정확한 분배함수
  Z(β) = Σ_k c_k e^{β(N − 2k)} = 2^N [ (2 cosh β)^N + (2 sinh β)^N ]
의 계수 확인이다 (고전 사실 · 2 차원 Z₂ 게이지는 풀린 모형).
  · 홀수 k 가 0 = 판 전체의 곱은 언제나 +1 (원환면에서 d₁ 의 상이 «합 0» 인 판 배치)
  · 게이지 변환 2^N 가운데 아무 고리도 바꾸지 않는 것은 둘 (상수 ±1) — ker d₀ = 2
  · 평평한 배치 (모든 판 +1) = 2^{N+1}
그래서 Z₂ 코사슬 0 → C⁰ → C¹ → C² → 0 (차원 N · 2N · N) 의 코호몰로지 크기는
  H⁰ = 2 · H¹ = 2^{N+1} / 2^{N−1} = 4 · H² = 2^N / 2^{N−1} = 2,  곧 베티 수 1 · 2 · 1 (원환면).
이 1 · 2 · 1 은 타원 곡선 (복소 원환면) 의 호지 다이아몬드 1 ; 1 1 ; 1 을 줄마다 더한 것과 같다 — 동서 축의 다리.

저자의 읽기 (수학 주장 아님) : 양–밀스 (게이지) 와 호지 (코호몰로지) 가 같은 셈의 두 얼굴. 질량 간극이나 4 차원 연속 극한은
이 파일과 관계없다 — 유한한 격자의 셈만 판정한다.
-/
set_option Elab.async false

namespace GaugeZ2

def bit (c k : Nat) : Nat := (c >>> k) % 2

/-- 판 p (= j·Lx + i) 의 값 (0 = +1, 1 = −1) -/
def plaq (Lx Ly c p : Nat) : Nat :=
  let N := Lx * Ly
  let i := p % Lx
  let j := p / Lx
  let h := fun (a b : Nat) => (b % Ly) * Lx + (a % Lx)
  (bit c (h i j) + bit c (N + h (i + 1) j) + bit c (h i (j + 1)) + bit c (N + h i j)) % 2

/-- 음의 판 수 -/
def negCount (Lx Ly c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun p acc => acc + plaq Lx Ly c p) (Lx * Ly)

/-- 막대 그림을 자연수 하나에 담음 : 칸 k 의 수는 2^{20k} 자리 -/
def hist (Lx Ly : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun c acc => acc + 1 <<< (20 * negCount Lx Ly c)) (2 ^ (2 * (Lx * Ly)))

/-- 바깥 줄 a0 … a0 + len − 1 (각 줄에 안쪽 2^N 개) 의 막대 그림 — 3 × 3 은 GaugeZ2Big 이 서른두 토막으로 셈 -/
def histChunk (Lx Ly a0 len : Nat) : Nat :=
  let N := Lx * Ly
  Nat.rec (motive := fun _ => Nat) 0 (fun a acc =>
    Nat.rec (motive := fun _ => Nat) acc (fun b acc' => acc' + 1 <<< (20 * negCount Lx Ly ((a0 + a) * 2 ^ N + b))) (2 ^ N)) len

def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

/-- 정확한 답 : 칸 k 에 2^{N+1} C(N, k) (k 짝수) -/
def expect (N : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun k acc => acc + (if k % 2 == 0 then 2 ^ (N + 1) * choose N k else 0) <<< (20 * k)) (N + 1)

/-- 게이지 변환 g (꼭짓점 비트) 가 만드는 고리 배치 -/
def gaugeLinks (Lx Ly g : Nat) : Nat :=
  let N := Lx * Ly
  Nat.rec (motive := fun _ => Nat) 0 (fun p acc =>
    let i := p % Lx
    let j := p / Lx
    let s := fun (a b : Nat) => (b % Ly) * Lx + (a % Lx)
    let hb := (bit g (s i j) + bit g (s (i + 1) j)) % 2
    let vb := (bit g (s i j) + bit g (s i (j + 1))) % 2
    acc + hb <<< p + vb <<< (N + p)) N

/-- ker d₀ : 고리를 하나도 바꾸지 않는 게이지 변환의 수 -/
def kerD0 (Lx Ly : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun g acc => acc + (if gaugeLinks Lx Ly g == 0 then 1 else 0)) (2 ^ (Lx * Ly))

/-- d₁ ∘ d₀ = 0 : 게이지로 만든 배치는 모두 평평 (음의 판 0) -/
def pureGaugeFlat (Lx Ly : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun g acc => acc && negCount Lx Ly (gaugeLinks Lx Ly g) == 0) (2 ^ (Lx * Ly))

/-! ## 1. 정확한 셈 (= 분배함수의 계수) -/

theorem count_2x2 : hist 2 2 = expect 4 := by decide +kernel
theorem count_2x3 : hist 2 3 = expect 6 := by decide +kernel

/-- 3 × 3 의 막대 : 1024 · 0 · 36864 · 0 · 129024 · 0 · 86016 · 0 · 9216 · 0 (합 2^18) -/
theorem expect_3x3_values :
    [choose 9 0, choose 9 2, choose 9 4, choose 9 6, choose 9 8].map (2 ^ 10 * ·) = [1024, 36864, 129024, 86016, 9216] ∧
    1024 + 36864 + 129024 + 86016 + 9216 = 2 ^ 18 := by decide

/-! ## 2. 게이지와 코호몰로지 -/

theorem kerD0_2x2 : kerD0 2 2 = 2 := by decide +kernel
theorem kerD0_2x3 : kerD0 2 3 = 2 := by decide +kernel
theorem kerD0_3x3 : kerD0 3 3 = 2 := by decide +kernel

theorem flat_2x2 : pureGaugeFlat 2 2 = true := by decide +kernel
theorem flat_2x3 : pureGaugeFlat 2 3 = true := by decide +kernel
theorem flat_3x3 : pureGaugeFlat 3 3 = true := by decide +kernel

/-- 베티 수 1 · 2 · 1 : |H⁰| = |ker d₀| = 2, |H¹| = |ker d₁| / |im d₀| = 2^{N+1} / (2^N / 2) = 4,
    |H²| = |C²| / |im d₁| = 2^N / (2^{2N} / 2^{N+1}) = 2  (N = 4 · 6 · 9) -/
theorem betti_121 :
    ([4, 6, 9].all fun N =>
      2 ^ (N + 1) / (2 ^ N / 2) == 2 ^ 2 && 2 ^ N / (2 ^ (2 * N) / 2 ^ (N + 1)) == 2 ^ 1) = true := by decide

/-- 대조 : 셈 틀을 하나 바꾸면 (k 홀수에도 2^{N+1} C(N,k) 를 넣으면) 맞지 않음 -/
def expectWrong (N : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun k acc => acc + (2 ^ (N + 1) * choose N k) <<< (20 * k)) (N + 1)
theorem control_wrong : hist 2 2 ≠ expectWrong 4 := by decide +kernel

end GaugeZ2
