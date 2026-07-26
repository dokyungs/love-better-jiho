#!/usr/bin/env bash
# 새 사진을 staging/ 에 넣은 뒤 이것만 실행하면 된다.
#   ./scripts/run_all.sh          정리 + 갤러리 재생성
#   ./scripts/run_all.sh serve    위 작업 후 편집 가능한 서버까지 실행
set -euo pipefail
cd "$(dirname "$0")/.."

python3 scripts/jiho.py all

if [ "${1:-}" = "serve" ]; then
  python3 scripts/jiho.py serve
else
  echo
  echo "갤러리:  open index.html"
  echo "편집:    python3 scripts/jiho.py serve   → http://127.0.0.1:8765/"
fi
