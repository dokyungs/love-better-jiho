#!/usr/bin/env bash
# 새 사진을 staging/ 에 넣은 뒤 이것만 실행하면 된다.
#   ./scripts/run_all.sh          정리 + 갤러리 재생성
#   ./scripts/run_all.sh serve    위 작업 후 편집 가능한 서버까지 실행
#   ./scripts/run_all.sh serve --lan   다른 기기에서도 접속 가능하게 실행
#   (serve 뒤에 붙인 옵션은 jiho.py serve 로 그대로 넘어간다)
set -euo pipefail
cd "$(dirname "$0")/.."

python3 scripts/jiho.py all

if [ "${1:-}" = "serve" ]; then
  shift
  python3 scripts/jiho.py serve "$@"
else
  echo
  echo "갤러리:  open index.html"
  echo "편집:    python3 scripts/jiho.py serve   → http://127.0.0.1:8765/"
  echo "공유:    python3 scripts/jiho.py serve --lan   → 같은 네트워크의 다른 기기에서도 접속"
fi
