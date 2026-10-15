#!/usr/bin/env bash
# Builds the paper and the release files:
#   dist/PolyaVinogradovLogLog_final2.pdf             the paper
#   dist/PolyaVinogradovLogLog_final2-tex.zip         LaTeX source with the figures as PNG
#   dist/PolyaVinogradovLogLog_final2-arxiv.tar.gz    the same source as an arXiv tarball
#   preprintPolyaVinogradovLogLog/PolyaVinogradovLogLog.pdf   the paper (only file there)
#   MasterPolyaVinogradovLogLog_masterzipfinal2.zip   every tracked file with dist/
set -euo pipefail
cd "$(dirname "$0")"
for t in latexmk zip tar git; do
  command -v "$t" >/dev/null || { echo "missing tool: $t" >&2; exit 2; }
done

name=PolyaVinogradovLogLog
master=Master${name}_masterzipfinal2.zip

(cd paper && latexmk -pdf -interaction=nonstopmode -halt-on-error pvloglog.tex >/dev/null)
if grep -E "Overfull|Underfull|undefined" paper/pvloglog.log; then
  echo "paper/pvloglog.log reports bad boxes or undefined references" >&2
  exit 1
fi

rm -rf dist
mkdir -p dist preprintPolyaVinogradovLogLog
cp paper/pvloglog.pdf "dist/${name}_final2.pdf"
cp paper/pvloglog.pdf "preprintPolyaVinogradovLogLog/${name}.pdf"

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

mkdir -p "$tmp/${name}_final2-tex/figures"
cp paper/pvloglog.tex "$tmp/${name}_final2-tex/"
cp paper/figures/*.png "$tmp/${name}_final2-tex/figures/"
(cd "$tmp" && zip -qr -X "${name}_final2-tex.zip" "${name}_final2-tex")
mv "$tmp/${name}_final2-tex.zip" dist/
tar -czf "dist/${name}_final2-arxiv.tar.gz" -C "$tmp/${name}_final2-tex" pvloglog.tex figures

mkdir "$tmp/Master${name}"
git ls-files -z | grep -zvE "^(dist/|${master}$)" \
  | xargs -0 -I{} cp --parents {} "$tmp/Master${name}/"
mkdir -p "$tmp/Master${name}/dist" "$tmp/Master${name}/preprintPolyaVinogradovLogLog"
cp dist/* "$tmp/Master${name}/dist/"
cp "preprintPolyaVinogradovLogLog/${name}.pdf" "$tmp/Master${name}/preprintPolyaVinogradovLogLog/"
rm -f "$master"
(cd "$tmp" && zip -qr -X "$master" "Master${name}")
mv "$tmp/$master" .
echo "built: $(ls dist | tr '\n' ' ')$master"
