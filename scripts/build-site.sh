#!/usr/bin/env bash
# Build the living research-status page from site/ into docs/, which GitHub
# Pages serves at https://mysticflounder.github.io/modular-schur/.
#
# Inputs:
#   site/content/index.md    the content (the only file with math/prose in it)
#   site/theme/template.html pandoc template carrying the page design
#   site/theme/style.css     the design's stylesheet
#   site/theme/vendor/katex/ vendored KaTeX (no CDN dependency at runtime)
#
# Output:
#   docs/index.html          generated; commit it, Pages serves from main:/docs
#   docs/assets/             generated copies of style.css and KaTeX
#
# Usage: scripts/build-site.sh [--serve]
#   --serve  build, then serve docs/ on http://localhost:8000 for a local look

set -euo pipefail

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SITE="$REPO/site"
OUT="$REPO/docs"

command -v pandoc >/dev/null || { echo "build-site: pandoc not found" >&2; exit 1; }

TITLE="Modular Schur numbers S_m(k,l): research status"
REPO_URL="https://github.com/mysticflounder/modular-schur"
# Content date, not build date: bump when the research state changes, so a
# no-op rebuild does not claim the status is fresher than it is.
UPDATED="$(sed -n 's/^updated: *//p' "$SITE/content/index.md" | head -1)"
[ -n "$UPDATED" ] || { echo "build-site: no 'updated:' field in site/content/index.md" >&2; exit 1; }

mkdir -p "$OUT/assets"
cp "$SITE/theme/style.css" "$OUT/assets/style.css"
rm -rf "$OUT/assets/katex"
cp -R "$SITE/theme/vendor/katex" "$OUT/assets/katex"
# Pages runs Jekyll by default, which would skip our assets/ and mangle braces.
touch "$OUT/.nojekyll"

pandoc "$SITE/content/index.md" \
  --from=markdown+tex_math_dollars+pipe_tables+footnotes+definition_lists \
  --to=html5 \
  --template="$SITE/theme/template.html" \
  --katex=assets/katex/ \
  --toc --toc-depth=2 \
  --section-divs \
  --metadata title="$TITLE" \
  --variable updated="$UPDATED" \
  --variable repo="$REPO_URL" \
  --output "$OUT/index.html"

echo "build-site: wrote $OUT/index.html (content dated $UPDATED)"

if [ "${1:-}" = "--serve" ]; then
  echo "build-site: serving $OUT at http://localhost:8000 (Ctrl-C to stop)"
  python3 -m http.server 8000 --directory "$OUT"
fi
