#!/usr/bin/env python3
"""Build and audit only the examples distributed in this repository."""
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
EXPECTED = {
    'Audit.lean': {'LeanBook.environment_check'},
    'examples/Volume3Exercises.lean': {
        'real_l2_inner', 'real_l2_norm_sq', 'complex_l2_inner',
        'unitIntervalMeasure', 'unitInterval_probability', 'unitCoordinate',
        'unitCoordinate_measurable', 'unitCoordinate_integrable',
        'unitCoordinate_sq_integrable', 'unitCoordinate_expectation',
        'unitCoordinate_second_moment', 'unitCoordinate_memLp',
        'unitCoordinateL2', 'unitCoordinateL2_ae', 'unitCoordinateL2_norm_sq',
    },
}


def run(*command):
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    print(result.stdout, end='')
    if result.returncode:
        raise SystemExit(result.stderr or result.stdout or f'Failed: {command}')
    return result.stdout


def main():
    output = ROOT / '.generated/verification.json'
    output.parent.mkdir(exist_ok=True)
    output.unlink(missing_ok=True)
    run('lake', 'build')
    run('lake', 'env', 'lean', '-DautoImplicit=false', '-DwarningAsError=true', 'Scratch.lean')
    reports = {}
    for filename, expected in EXPECTED.items():
        text = run('lake', 'env', 'lean', '-DautoImplicit=false', '-DwarningAsError=true', filename)
        found = {}
        # Each requested declaration must appear exactly once and use only standard axioms.
        for match in re.finditer(r"'([^']+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])", text):
            name, raw = match.groups()
            if name in found:
                raise SystemExit(f'Duplicate axiom output: {name}')
            axioms = [] if raw is None else [item.strip() for item in raw.split(',') if item.strip()]
            if set(axioms) - ALLOWED:
                raise SystemExit(f'Unapproved axioms for {name}: {axioms}')
            found[name] = axioms
        if set(found) != expected:
            raise SystemExit(f'Axiom coverage mismatch in {filename}: {set(found) ^ expected}')
        reports[filename] = {'sha256': hashlib.sha256((ROOT / filename).read_bytes()).hexdigest(), 'axioms': found}
    output.write_text(json.dumps({'status': 'passed', 'audited_declarations': 16, 'files': reports}, indent=2) + '\n')
    print('Passed: learning project, Scratch.lean, and 16 audited declarations.')


if __name__ == '__main__':
    main()
