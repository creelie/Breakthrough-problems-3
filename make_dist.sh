#!/usr/bin/env bash
# Builds dist/: the paper PDF, the arXiv tarball and MasterVinogradovPrimitiveRootZip.zip.
set -euo pipefail
cd "$(dirname "$0")"
command -v zip >/dev/null || { echo "missing tool: zip" >&2; exit 2; }
mkdir -p dist
cp paper/primroot.pdf dist/primroot.pdf
tar -czf dist/primroot-arxiv.tar.gz -C paper primroot.tex
rm -f dist/MasterVinogradovPrimitiveRootZip.zip
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
mkdir "$tmp/MasterVinogradovPrimitiveRoot"
git ls-files -z | grep -zv '^dist/MasterVinogradovPrimitiveRootZip.zip$' \
  | xargs -0 -I{} cp --parents {} "$tmp/MasterVinogradovPrimitiveRoot/"
cp dist/primroot.pdf dist/primroot-arxiv.tar.gz "$tmp/MasterVinogradovPrimitiveRoot/dist/" 2>/dev/null \
  || { mkdir -p "$tmp/MasterVinogradovPrimitiveRoot/dist"; cp dist/primroot.pdf dist/primroot-arxiv.tar.gz "$tmp/MasterVinogradovPrimitiveRoot/dist/"; }
(cd "$tmp" && zip -qr -X MasterVinogradovPrimitiveRootZip.zip MasterVinogradovPrimitiveRoot)
mv "$tmp/MasterVinogradovPrimitiveRootZip.zip" dist/
echo "dist/ ready: $(ls dist | tr '\n' ' ')"
