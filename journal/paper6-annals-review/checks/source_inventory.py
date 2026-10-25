"""Inventory bundled proof sources and check their nonstandard import closure.

This checks source completeness and hashes, not mathematical validity. The
kernel audit is a separate gate. Run from any directory in the repository.
"""
from pathlib import Path
import hashlib
import json
import re
import sys

ROOT = Path(__file__).resolve().parents[3]
LEAN = ROOT / 'lean'
LOCAL_ROOTS = ('OAI', 'PrimeNumberTheoremAnd', 'RellichKondrachov', 'Vinogradov')
STANDARD_ROOTS = {'Mathlib', 'Lean', 'Init', 'Std', 'Lake', 'Batteries', 'Aesop',
                  'Qq', 'Plausible', 'ProofWidgets', 'LeanSearchClient',
                  'ImportGraph', 'Cli'}


def without_comments(s):
    """Remove nested Lean block comments and line comments before imports."""
    out = []
    depth = 0
    i = 0
    while i < len(s):
        if s.startswith('/-', i):
            depth += 1
            i += 2
        elif depth and s.startswith('-/', i):
            depth -= 1
            i += 2
        elif depth:
            if s[i] == '\n':
                out.append('\n')
            i += 1
        elif s.startswith('--', i):
            end = s.find('\n', i)
            i = len(s) if end < 0 else end
        else:
            out.append(s[i])
            i += 1
    assert depth == 0, 'Unterminated block comment'
    return ''.join(out)


def inventory():
    paths = sorted(list(LEAN.glob('*.lean')) +
                   [p for root in LOCAL_ROOTS for p in (LEAN / root).rglob('*.lean')])
    modules = {'.'.join(p.relative_to(LEAN).with_suffix('').parts): p for p in paths}
    entries = []
    for name, path in modules.items():
        imports = []
        for line in without_comments(path.read_text(encoding='utf-8')).splitlines():
            match = re.match(r'^\s*(?:(?:public|private|meta)\s+)?import\s+(.+)$', line)
            if match:
                imports.extend(match.group(1).split())
        for imported in imports:
            head = imported.split('.')[0]
            assert head in LOCAL_ROOTS + tuple(STANDARD_ROOTS), (name, imported)
            if head in LOCAL_ROOTS:
                assert imported in modules, f'Missing bundled module: {name} -> {imported}'
        entries.append({'path': path.relative_to(ROOT).as_posix(),
                        'sha256_lf': hashlib.sha256(path.read_bytes().replace(b'\r\n', b'\n')).hexdigest(),
                        'imports': imports})
    manifest = json.loads((LEAN / 'lake-manifest.json').read_text())
    return {'status': 'PASS',
            'scope': 'Bundled nonstandard proof-source import closure and SHA-256 after CRLF-to-LF normalization; not a kernel audit.',
            'lean_toolchain': (LEAN / 'lean-toolchain').read_text().strip(),
            'local_roots': list(LOCAL_ROOTS),
            'source_count': len(entries),
            'root_counts': {r: sum(x['path'].startswith('lean/' + r + '/')
                                   or x['path'] == 'lean/' + r + '.lean' for x in entries)
                            for r in LOCAL_ROOTS},
            'standard_libraries': [{'name': x['name'], 'url': x['url'], 'commit': x['rev']}
                                   for x in manifest['packages']],
            'files': entries}


if __name__ == '__main__':
    result = inventory()
    target = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).resolve().parents[1] / 'verification/source-inventory.json'
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({k: v for k, v in result.items() if k != 'files'}))
