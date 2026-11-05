# KIMBANJI v2.0 — v2/ 폴더 (added modules)

## 한국어

- 이 폴더는 KIMBANJI 1.0 (2026-10-28, 정리 1,701 개 · 모듈 60 개)의 파일을 하나도 바꾸지 않고, 그 뒤 트롬보 등록 장부(2026-10-31 시작)에 등록된 묶음에서 가져온 린 모듈 31 개를 더한 것이다. 선언된 theorem/lemma 는 모두 443 개다(정리 수는 모듈 원문의 선언을 센 값이며 커널 재빌드로 다시 세지 않았다).
- 라이선스: 이 폴더(v2/)의 파일은 CC BY-NC 4.0 으로 공개한다(영리 목적은 THROMBO PROTOCOL 과 별도 유료 라이선스). 1.0 의 KIMBANJI 원문 71 항목은 CC0 1.0 그대로다. 파일 안에 제3자 저작권 표시나 다른 라이선스 표기가 있는 모듈은 이 폴더에 넣지 않았다(아래 «넣지 않은 것»).
- 빌드: 1.0 의 lakefile 은 이 폴더를 짓지 않는다. 대부분의 모듈은 Mathlib 이 필요하며, 각 모듈은 등록 묶음 안에서 그 묶음의 도구 버전으로 지어졌다(각 묶음의 로그 참조). 이 판을 만들 때 다시 짓지는 않았다.
- 점검: 주석과 문자열을 뺀 원문에서 sorry · admit · axiom 선언 · native_decide · unsafe · set_option 을 찾았고, 넣은 모듈에는 하나도 없다. 같은 내용의 파일은 하나만 넣었고, 이름이 같고 내용이 다르면 나중 묶음의 것을 넣었다.
- 어느 모듈도 밀레니엄 문제의 해결을 주장하지 않는다. 대부분은 알려진 정리의 형식화, 동치 명제, 유한한 확인이다.

## English

- This folder leaves every file of KIMBANJI 1.0 (2026-10-28, 1,701 theorems in 60 modules) unchanged and adds 31 Lean modules taken from bundles registered afterwards in the Thrombo registration ledger (begun 2026-10-31). They declare 443 theorem/lemma items in total (counted from the source declarations, not recounted by a kernel rebuild).
- Licence: the files in this folder (v2/) are released under CC BY-NC 4.0 (commercial use requires a separate paid licence from THROMBO PROTOCOL). The 71 entries of the 1.0 KIMBANJI sources remain CC0 1.0. Modules containing third-party copyright notices or other licence statements were not placed in this folder (see "Not included").
- Building: the 1.0 lakefile does not build this folder. Most modules need Mathlib; each was built inside its registration bundle with that bundle's toolchain (see the bundle logs). They were not rebuilt for this release.
- Checks: after stripping comments and strings, the sources were searched for sorry · admit · axiom declarations · native_decide · unsafe · set_option; none occurs in the included modules. Files with identical content are included once; for equal names with different content, the later bundle's file is included.
- No module claims a solution of any Millennium problem. Most are formalizations of known theorems, equivalent statements and finite checks.

## 모듈 목록 / Modules

| 파일 / file | 묶음 / bundle | 블록 / block | theorem·lemma | 가져오기 / imports | 폴더에 없는 의존 / missing deps | SHA-256 |
|---|---|---|---|---|---|---|
| Trombo_ABC_FLT6.lean | Mathlib_사다리 | 974125 | 3 | Mathlib | — | `e2599f9697ccc12653cbd860e933f469b2ebd0409ab2b0fb7453e7c2c1d49282` |
| Trombo_Chi3Sine.lean | Mathlib_사다리 | 974125 | 4 | Mathlib | — | `8c91b6cf14803849c609ec4c5a5031276d900d28ebadfe825b9da0a588681baf` |
| Trombo_Eisenstein.lean | Mathlib_사다리 | 974125 | 5 | Mathlib | — | `14f3e978fa8dd5818dcb9520701520ea079779deb37559ee52d132c9c8922b14` |
| Trombo_L1Chi3.lean | Mathlib_사다리 | 974125 | 20 | Mathlib | — | `75ceab81bf9ee5ff2dc386a35ac593e16e9b7a1ec0ee1bff41be785c3d34d4af` |
| Trombo_GRH.lean | Mathlib_사다리2 | 974128 | 2 | Mathlib | — | `bd163235df89337850ec487ffd0313194cbbcebaf193f78fe852ac43e8f54cf0` |
| Trombo_Gaps.lean | Mathlib_사다리2 | 974128 | 11 | Mathlib | — | `0c254fa2ce35f7d9149a37435240b5fed33e8034533f90146d729778aff66fa0` |
| Trombo_HL.lean | Mathlib_사다리2 | 974128 | 5 | Mathlib | — | `7b515fb880110529f4c092c21522d111a2eab44d05372aca9777892bafe66d72` |
| Trombo_Congruent.lean | Mathlib_사다리3 | 974128 | 9 | Mathlib | — | `867fd6ee6a23fc62b0688dff4ef5ae5da5148c78806b6dc3313dd0faecad1f91` |
| Trombo_Mertens.lean | RH_Mertens_동치 | 974136 | 12 | Mathlib | — | `105df562dd9a142f8416de2e8d2dad5e6bf2e6b0e9664d3549d9ea7fb8fcc451` |
| Trombo_RHEquiv.lean | Mathlib_사다리4 | 974134 | 22 | Mathlib | — | `94d85bd5e862f1042f2c4652fa5892469448a25efda5d759e1d9259a8a5e6a3f` |
| Trombo_RHtoMertens.lean | Mathlib_사다리4 | 974134 | 14 | Mathlib | — | `1826f92862cbe9096187c7de5975e1b63344af71f147bbbd353a06ffcaec907f` |
| Trombo_PerronMoebius.lean | RH_Mertens_동치 | 974136 | 5 | Mathlib | Trombo_PerronVendor, Trombo_ZetaLogBound | `614b6eef500e3ff9c4725a908102cec6dc3c19cd2af9590e42751da08dead0ac` |
| Trombo_RHMertens.lean | RH_Mertens_동치 | 974136 | 14 | Mathlib | Trombo_ZetaLogBound | `79b223af35570da7fb2b0664ae063bf77b195532cde1bda97ab6481058db7774` |
| Trombo_RHMertensEquiv.lean | RH_Mertens_동치 | 974136 | 3 | Trombo_Mertens, Trombo_RHMertens | — | `774c812a6240288ae68db9d74f646c57910e84b1d3f16e83ed7761e07d18f4ff` |
| Trombo_ZeroQuartet.lean | ZeroQuartet_네쌍둥이 | 974139 | 24 | Mathlib | — | `f39628185efad35c26358d5b9414a71ab96480aaccb0afe227fa970c3ad1b333` |
| Kimbanji_Needle.lean | 뷔퐁라이프니츠_2026-11-04 | 974519 | 10 | Mathlib | — | `24e5d1f2f1c4a932aa18f33b7c6107a904d71a7de3e4a62a9291332bef4884b4` |
| Kimbanji_PhiPi.lean | 황금비파이심화_2026-11-04 | 974522 | 35 | Mathlib | — | `78d080b4da6c34d3a654592be599b8d4ac005a4a7ecac30483df43cae5a73884` |
| Kimbanji_CubeNets.lean | 호지11큐브11_2026-11-04 | 974522 | 17 | core Lean | — | `581db0cac89f49e9a2863cd41be763d0631304066ee0d7fc9df2e7463e27c48e` |
| Kimbanji_Entangle.lean | 푸리에숨은원_2026-11-04 | 974522 | 12 | Mathlib | — | `9e520c8541272c4d7d13e1a39e019e68f464ce5812467e73091a761265dea126` |
| Kimbanji_FourierHub.lean | 푸리에숨은원_2026-11-04 | 974522 | 19 | Mathlib | — | `a77cd0f0c5ef5155f8d329b79acbf48818e147b9bfaf6a5b9697d97b67c67ac4` |
| Kimbanji_CubeFill.lean | 큐브빈칸공정_2026-11-04 | 974525 | 14 | Mathlib | — | `eba6890e319750cbb74fecdb13b67f381f3a4938856f8cc0235a167e68719df1` |
| Kimbanji_CubeRelax.lean | 큐브기준완화_2026-11-04 | 974530 | 9 | Mathlib | — | `ddd369a3ff5191702e7a1d4b234febaad7fed42e5971537b0d430a6377ece5eb` |
| Kimbanji_Slab78.lean | 띠큐브78_2026-11-04 | 974530 | 29 | Mathlib | — | `a3205ffdabe984742e55640f55a9d695c06e1432870ab9e2e2b7a43b36dcc9dd` |
| Kimbanji_CandH.lean | 후보H닫기_2026-11-04 | 974530 | 26 | Mathlib | — | `487620f1b09f3cebb9fe3b69717bd25df6c091a061f8a7b9ddc35fd083b11226` |
| Kimbanji_CubeLit.lean | 큐브문헌채움_2026-11-04 | 974530 | 41 | Mathlib | — | `3706c8befed4900eab101ef9e42269e1d491a1eab8480f52aa1db40416442e9d` |
| Kimbanji_CubeLayout.lean | 상수큐브새배치_2026-11-04 | 974536 | 29 | Mathlib | — | `0da7806bf822638e49874382e63928861aa7d7a08d32df1349232e6671d9c6d1` |
| Kimbanji_EggCRT.lean | 달걀CRT사영_2026-11-04 | — | 9 | Mathlib | — | `b1016561a4137a4a5ee46a8319e36143f3a5b77e6632f56b58d0d3afb477cba6` |
| KimbanjiHints.lean | 힌트목록페이블판_2026-11-04 | 974558 | 6 | Mathlib | — | `72b4bf7282ff62a29fbb2aefb8d6d71a3f830a25d1ee59c3ef54b002a5c39105` |
| KimbanjiWilliams.lean | 원문확인_윌리엄스선선_2026-11-04, 밀레니엄판마무리판_2026-11-04 | 974562 | 8 | Mathlib | — | `6c4302be6706a0d5f11e6229f52e1907dca6d645e863a5729e3881af28465961` |
| KimbanjiInsideRH.lean | 안과밖같은트롬보_2026-11-04 | — | 17 | Mathlib | — | `8aecbbfd8c785c05a07196c605a0cb2d99389cc728344c2b2bb760973b5fd997` |
| KimbanjiCubeBridge.lean | 큐브다리지도_2026-11-04 | — | 9 | Mathlib | — | `d6f89169c5413e4696f8a961103231d296e496b1998d3bd780d33da8d400890d` |

«—» = 장부에 블록 번호가 아직 없음(OTS 대기) / no block number in the ledger yet (pending). Trombo_Mertens.lean 은 RH_Mertens_동치 판이며 Mathlib_사다리3 의 같은 이름 파일을 대신한다 / is the RH_Mertens_동치 version and supersedes the file of the same name in Mathlib_사다리3. Trombo_PerronMoebius · Trombo_RHMertens 는 아래 «넣지 않은 것» 의 모듈에 기대므로 이 폴더만으로는 지어지지 않는다 / depend on modules listed under "Not included" and do not build from this folder alone.

## 넣지 않은 것 / Not included

- Trombo_Check.lean (RH_Mertens_동치): 금지 토큰/forbidden token: set_option
- 머리말에 «THROMBO PROTOCOL WNH 1.0» 표기 또는 제3자 저작권 · Apache-2.0 표기가 있어 이 폴더에 넣지 않은 모듈 / modules carrying a "THROMBO PROTOCOL WNH 1.0" header or third-party copyright · Apache-2.0 notices, kept out of this folder (licence to be decided by the author):
  - Trombo_AllInOne.lean (RH_Mertens_동치)
  - Trombo_PerronVendor.lean (RH_Mertens_동치)
  - Trombo_ZetaLogBound.lean (RH_Mertens_동치)
  - Trombo_ThetaMertens.lean (Theta_Mertens)
  - Trombo_PsiRH.lean (PsiRH_ψ동치)
  - Trombo_PiLi.lean (PiLi_π−li동치)
  - Trombo_Gronwall.lean (Gronwall_그론월)
  - Trombo_Nicolas.lean (Nicolas_니콜라)
  - Trombo_NicolasLandau.lean (Nicolas_란다우)
  - Trombo_NicolasRH.lean (Nicolas_RH다리)
  - Trombo_NicolasRHHalf.lean (Nicolas_RH반쪽)
  - Trombo_RobinLemma2.lean (Nicolas_로빈보조2)
  - Trombo_ZeroSum.lean (Nicolas_영점합)
  - Trombo_RobinNicolas.lean (Nicolas_RH동치)
  - Trombo_NicolasTheorem2.lean (Nicolas_정리2, RH_네판정, Nicolas_정리3, RH_비범한수, RH_세얼굴)
  - Trombo_Gauge.lean (Gauge_게이지구조)
  - Trombo_Tunnell.lean (BSD_터널표N200)
  - Kimbanji_HwatuGF.lean (화투_점수생성함수_2026-11-03)
  - Kimbanji_HodgeBridge.lean (호지_다리_2026-11-04)
  - Kimbanji_SixSpiral.lean (여섯갈래_소수나선_2026-11-04)
  - Kimbanji_Li1.lean (RH_양성구조_2026-11-04)
  - Kimbanji_LiPos.lean (RH_리계수Lean_2026-11-04)
  - Kimbanji_GaltonGauss.lean (상수큐브갈턴_2026-11-04)
  - Kimbanji_CubeEdges.lean (트롬보큐브통합_2026-11-04)
  - Kimbanji_TwoLoop.lean (쌍고리곡면종수2_2026-11-04)



## 추가 (2026-11-05) / Added
- KimbanjiMirrorTwist.lean — 거울 정리: E₁(−a) 는 E₁(a)/⟨P⟩ 의 −3 꼬임(모든 a) / mirror theorem: E₁(−a) is the −3 twist of E₁(a)/⟨P⟩ for all a (Mathlib · ring; axioms propext, Quot.sound). 묶음 거울정리_모든a_2026-11-05 (2fb07cd7).
