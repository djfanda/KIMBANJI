#!/bin/bash
# 김반지 (KIMBANJI) — 누구나 같은 커널로 다시 확인한다.  쓰임 : bash KIMBANJI_check.sh
# 1) 원문 지문이 KIMBANJI.sha256 과 같은지  2) 린 4 커널로 모든 정리를 다시 짓기(lake build)
set -u
export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")" || exit 1
echo "1. 원문 지문"; sha256sum -c --quiet KIMBANJI.sha256 && echo "   모두 같음 ($(wc -l < KIMBANJI.sha256) 파일)" || { echo "   다른 파일이 있음"; exit 1; }
echo "2. 린 커널로 다시 짓기 (한 모듈씩 — 가장 큰 모듈이 약 5.5 GB 의 메모리를 씀)"
: > KIMBANJI_build.log
for m in $(grep '^import ' Trombo.lean | awk '{print $2}'); do
  if lake build "$m" >> KIMBANJI_build.log 2>&1; then echo "   ✔ $m"; else echo "   ✖ $m — KIMBANJI_build.log 를 볼 것"; exit 1; fi
done
lake build >> KIMBANJI_build.log 2>&1 || { echo "   ✖ Trombo"; exit 1; }
echo "   $(tail -1 KIMBANJI_build.log)"
echo "3. 정리 수 (공리 감사 목록) : $(grep -c '^#print axioms' KIMBANJI_axioms.lean) · 모듈 $(grep -c '^import ' Trombo.lean)"
echo "4. 공리 감사 (모든 정리가 기대는 공리 — 빈칸 sorryAx 가 있으면 실패)"
lake env lean KIMBANJI_axioms.lean > KIMBANJI_axioms.log 2>&1 || { echo "   ✖ 공리 감사 실패"; exit 1; }
n=$(grep -c "depends on axioms\|does not depend" KIMBANJI_axioms.log); bad=$(grep -c "sorryAx\|ofReduceBool" KIMBANJI_axioms.log)
echo "   정리 $n 개 · sorryAx · native 0 이어야 함 : $bad"
[ "$bad" = 0 ] || exit 1
