#!/usr/bin/env python3
"""Reproduce the proof and arithmetic checks for the sparse-triple manuscript."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--full', action='store_true', help='also build the root library')
    parser.add_argument('--output-dir', type=Path, default=Path('/tmp/ramanujan-quintuple-review'))
    parser.add_argument('--record', type=Path, default=ROOT/'docs/verification/quintuple_review.json')
    args = parser.parse_args()
    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=True)
    commands = []

    def run(command, label):
        path = output/f'{label}.log'
        with path.open('w') as log:
            result = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
        if result.returncode:
            raise SystemExit(f'{label} failed (exit {result.returncode}); see {path}')
        commands.append({'command': command, 'exit_code': result.returncode, 'log': path.name})
        print(f'{label}: passed', flush=True)
        return path.read_text()

    public_audits = []
    if args.full:
        public_output = output/'public'
        run([sys.executable, 'scripts/verify_lean.py', '--full', '--output-dir', str(public_output)],
            'full-public-verification')
        for name in ('forty11', 'bosonic_fock', 'celebrated_targets'):
            text = (public_output/f'{name}.axioms.txt').read_text()
            public_audits.append({'name': name,
                'declarations': len(re.findall(r'depends on axioms:', text))+
                                len(re.findall(r'does not depend on any axioms', text)),
                'output_sha256': hashlib.sha256(text.encode()).hexdigest()})
    else:
        for module in ('RamanujanTau.MultiQuintupleCenteredRoots',
                       'RamanujanTau.MultiQuintupleFourNinetySevenConverse'):
            run(['lake', 'build', module], f'build-{module}')
    audit = 'scripts/audit/quintuple_review.lean'
    report = run(['lake', 'env', 'lean', audit], 'axioms')
    expected = len(re.findall(r'^#print axioms ', (ROOT/audit).read_text(), re.M))
    reports = re.findall(r'depends on axioms: \[([^]]*)\]', report)
    reports += ['']*len(re.findall(r'does not depend on any axioms', report))
    axioms = {a.strip() for item in reports for a in item.split(',') if a.strip()}
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    if len(reports) != expected or axioms-allowed:
        raise SystemExit(f'axiom audit incomplete or unexpected dependencies: {axioms-allowed}')
    audit_output = ROOT/'docs/verification/quintuple_review.axioms.txt'
    audit_output.write_text(report)
    checked = ROOT/'docs/verification/quintuple_review_checks.json'
    run([sys.executable, 'scripts/check_quintuple_review.py', '--output', str(checked)], 'independent-coefficients')
    short_report = output/'short-generators.json'
    run([sys.executable, 'scripts/check_short_watson_generators.py',
         'docs/verification/short_watson_generators.json', '--output', str(short_report)], 'short-generators')
    source_paths = sorted((ROOT/'RamanujanTau').glob('MultiQuintuple*.lean'))
    source_paths += sorted((ROOT/'RamanujanTau/MultiQuintupleFourNinetySeven').glob('*.lean'))
    source_paths += [ROOT/p for p in (
        'RamanujanTau.lean', 'lean-toolchain', 'lakefile.toml', 'lake-manifest.json', audit,
        'scripts/verify_lean.py', 'scripts/audit/forty11.lean',
        'scripts/audit/bosonic_fock.lean', 'scripts/audit/celebrated_targets.lean',
        'scripts/classify_sparse_triple.py', 'scripts/check_quintuple_review.py',
        'scripts/generate_four97_converse.py', 'scripts/verify_quintuple_review.py',
        'scripts/quintuple_vanishing_scan.py', 'scripts/check_short_watson_generators.py',
        'docs/verification/short_watson_generators.json',
        'docs/paper/sparse-triples.tex', 'output/pdf/sparse-triples.pdf')]
    arithmetic = json.loads(checked.read_text())
    record = {
        'verified_at_utc': datetime.now(timezone.utc).isoformat(),
        'source_base_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
        'lean_toolchain': (ROOT/'lean-toolchain').read_text().strip(),
        'build_mode': 'Incremental build using pinned dependencies and existing local artifacts; all required targets checked.',
        'scope': 'Full root build' if args.full else 'Focused quintuple targets',
        'commands': commands,
        'public_audits': public_audits,
        'audit': {'declarations': len(reports), 'axioms': sorted(axioms),
                  'output': str(audit_output.relative_to(ROOT)),
                  'output_sha256': hashlib.sha256(audit_output.read_bytes()).hexdigest()},
        'independent_checks': {'triple_census': arithmetic['triple_census'],
                               'four97_witnesses': len(arithmetic['four97']['nonzero_witnesses']),
                               'four97_optimal_cutoff': 15,
                               'short_generators': json.loads(short_report.read_text())},
        'limits': ['No general four-factor converse is claimed.',
                   'The Python classifier is not extracted Lean code.',
                   'Independent mathematical review and a complete priority review remain outstanding.'],
        'literature_compared': [
            'https://arxiv.org/html/2603.04666v1',
            'https://arxiv.org/html/2606.06701v1',
            'https://arxiv.org/abs/2208.09882',
            'https://www.wcupa.edu/sciences-mathematics/mathematics/jMcLaughlin/'],
        'literature_review_scope': [
            'The 2026 papers were checked for product conventions, main theorem scope, and concluding examples.',
            'The Chern-Tang abstract was checked; a theorem-by-theorem comparison remains outstanding.',
            'The author publication list was checked for the announced higher-factor follow-up; no separate entry was identified.',
            'This selective search does not establish mathematical priority.'],
        'source_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in source_paths},
    }
    args.record.parent.mkdir(parents=True, exist_ok=True)
    args.record.write_text(json.dumps(record, indent=2)+'\n')
    print(f'{len(reports)} declarations audited; record: {args.record}', flush=True)


if __name__ == '__main__':
    main()
