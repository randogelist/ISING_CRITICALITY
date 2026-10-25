#!/usr/bin/env python3
"""Independent exact-rational audit of C++ Dlog-Pade arithmetic; not a physical proof."""
import argparse
import csv
from decimal import Decimal as D, localcontext
from fractions import Fraction as F
import hashlib
import io
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def exact_denominator(f, L, M):
    a = [[f[L+1+i-j] if L+1+i-j >= 0 else F(0)
          for j in range(1, M+1)] + [-f[L+1+i]] for i in range(M)]
    for i in range(M):
        pivot = max(range(i, M), key=lambda j: abs(a[j][i]))
        a[i], a[pivot] = a[pivot], a[i]
        if not a[i][i]:
            raise ArithmeticError('Exactly singular Pade system')
        for j in range(i+1, M):
            factor = a[j][i] / a[i][i]
            for k in range(i, M+1):
                a[j][k] -= factor*a[i][k]
    q = [F(1)] + [F(0)]*M
    for i in range(M-1, -1, -1):
        q[i+1] = (a[i][M]-sum(a[i][j]*q[j+1]
                             for j in range(i+1, M))) / a[i][i]
    return q


def poly(c, x):
    result = D(0)
    for a in reversed(c):
        result = result*x+a
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binary', default=str(ROOT/'build/pcd'))
    args = parser.parse_args()
    data_path = ROOT/'data/ising3d_susceptibility.json'
    data = json.loads(data_path.read_text())
    ht20_path = ROOT/'data/ising_susceptibility_ht20.csv'
    ht20 = {int(row['d']): [row[f'c{i}'] for i in range(21)]
            for row in csv.DictReader(io.StringIO(ht20_path.read_text()))}
    errors = []
    counts = {}
    with localcontext() as ctx:
        ctx.prec = 80
        for d in range(3, 12):
            coefficients = data['coefficients'] if d == 3 else ht20[d]
            scale = 2*d-1
            c = [F(int(v), scale**i) for i, v in enumerate(coefficients)]
            f = []
            for n in range(len(c)-1):
                f.append((n+1)*c[n+1]-sum(c[k]*f[n-k] for k in range(1, n+1)))
            output = subprocess.check_output([args.binary, '--pade-details', '--d', str(d)], text=True)
            rows = list(csv.DictReader(io.StringIO(output)))
            counts[d] = 0
            for row in rows:
                if row['accepted'] != 'true':
                    continue
                L, M = int(row['L']), int(row['M'])
                exact = exact_denominator(f, L, M)
                q = [D(a.numerator)/D(a.denominator) for a in exact]
                dq = [i*q[i] for i in range(1, len(q))]
                x = D(row['v'])*scale
                for _ in range(8):
                    x -= poly(q, x)/poly(dq, x)
                v = x/scale
                if not 0 < v < 1:
                    raise ArithmeticError('Refinement left physical interval')
                p = 2*v/(1+v)
                error = abs(p-D(row['p']))
                errors.append(error)
                counts[d] += 1
            if counts[d] == 0:
                raise ArithmeticError(f'No approximants checked at dimension {d}')
        if not errors or max(errors) >= D('1e-14'):
            raise ArithmeticError(f'C++ arithmetic comparison failed: {errors}')
    result = {
        'result': 'PASS',
        'cpp_arithmetic': 'GCC __float128, 113 binary significand bits',
        'oracle': 'Python Fraction exact Pade systems plus Decimal(80) Newton refinement of each reported simple pole',
        'approximants': len(errors),
        'counts_by_dimension': counts,
        'maximum_p_discrepancy': str(max(errors)),
        'header_sha256': hashlib.sha256((ROOT/'numerics/pade.hpp').read_bytes()).hexdigest(),
        'coefficient_data_sha256': hashlib.sha256(data_path.read_bytes()).hexdigest(),
        'ht20_data_sha256': hashlib.sha256(ht20_path.read_bytes()).hexdigest(),
        'ht20_header_sha256': hashlib.sha256((ROOT/'numerics/susceptibility_data.hpp').read_bytes()).hexdigest(),
        'scope': 'Arithmetic consistency only. Does not certify root selection, asymptotic convergence, or physical p_c error.'
    }
    (ROOT/'audit/pade-oracle.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
