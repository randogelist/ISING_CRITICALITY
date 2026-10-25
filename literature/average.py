#!/usr/bin/env python3
"""Reproducible descriptive literature means; no model outputs enter weighting."""
import argparse
import csv
from decimal import Decimal, localcontext
import hashlib
import io
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / 'data/benchmarks.json'
POLICY = Path(__file__).with_name('policy.json')
D = Decimal


def _number(value):
    return value if isinstance(value, D) else D(str(value))


def _matches(row, match):
    return all(row.get(key) == value for key, value in match.items())


def _convert(variable, value):
    """Convert the source's printed central value or uncertainty endpoint to p."""
    x = _number(value)
    if variable == 'p':
        return x
    if variable in ('K_Ising', 'beta_BB'):
        exponent = -2*x
    elif variable == 'K_Potts':
        exponent = -x
    elif variable == 'T_Ising':
        exponent = -2/x
    elif variable == 'T_Potts':
        exponent = -1/x
    else:
        raise ValueError('Unsupported source variable: '+variable)
    return 1-exponent.exp()


def _prepare(row, source):
    item = dict(row)
    item['source_url'] = source['url']
    item['source_type'] = source['type']
    item['source_location'] = source['location']
    if row['d'] == 2 and row.get('p_uncertainty') == 0:
        root = D(row['q']).sqrt()
        item.update(p=root/(1+root), u=D(0), p_low=root/(1+root),
                    p_high=root/(1+root), exact=True)
        return item
    x = _number(row['original_value'])
    error = row.get('original_uncertainty')
    if error is None or _number(error) <= 0:
        raise ValueError('A non-exact estimate needs a positive quoted error')
    error = _number(error)
    central = _convert(row['original_variable'], x)
    endpoints = sorted(_convert(row['original_variable'], x+sign*error)
                       for sign in (-1, 1))
    item.update(p=central, p_low=endpoints[0], p_high=endpoints[1],
                u=(endpoints[1]-endpoints[0])/2, exact=False)
    return item


def _mean(rows):
    """One entry per source; exact results take precedence over finite errors."""
    if not rows:
        return dict(status='missing', p_mean=None, source_count=0,
                    contributions=[])
    exact = [r for r in rows if r['exact']]
    if exact:
        if any(r['p'] != exact[0]['p'] for r in exact):
            raise ValueError('Conflicting exact references')
        chosen = exact[0]
        return dict(status='exact', p_mean=chosen['p'], source_count=1,
                    contributions=[dict(source_id=chosen['source_id'],
                                        p_value=chosen['p'], p_error=D(0),
                                        nominal_weight=None, normalized_weight=D(1))])
    ids = [r['source_id'] for r in rows]
    if len(set(ids)) != len(ids):
        raise ValueError('Duplicate source for one target; an explicit policy is required')
    weights = [1/(r['u']*r['u']) for r in rows]
    total = sum(weights, D(0))
    mean = sum((w*r['p'] for w, r in zip(weights, rows)), D(0))/total
    contributions = [dict(source_id=r['source_id'], p_value=r['p'], p_error=r['u'],
                          nominal_weight=w, normalized_weight=w/total)
                     for w, r in zip(weights, rows)]
    return dict(status='single' if len(rows) == 1 else 'weighted', p_mean=mean,
                source_count=len(rows), contributions=contributions)


def _compute(data=None, policy=None):
    if data is None:
        data = json.loads(DATA.read_text(), parse_float=D)
    if policy is None:
        policy = json.loads(POLICY.read_text())
    with localcontext() as context:
        context.prec = policy['arithmetic_precision_decimal_digits']
        prepared = [_prepare(row, data['sources'][row['source_id']])
                    for row in data['benchmarks']]
        for rule in policy['exclusions']:
            found = [r for r in prepared if _matches(r, rule['match'])]
            if len(found) != 1:
                raise ValueError('Exclusion must match exactly one row: '+str(rule['match']))
            found[0]['excluded_reason'] = rule['reason']
        results = {}
        for q in range(1, 4):
            for d in range(2, 12):
                target = [r for r in prepared if (r['q'], r['d']) == (q, d)]
                included = [r for r in target if not r.get('excluded_reason')]
                result = dict(q=q, d=d, **_mean(included))
                result['excluded'] = [dict(source_id=r['source_id'],
                                           original_printed=r['original_printed'],
                                           reason=r['excluded_reason'])
                                      for r in target if r.get('excluded_reason')]
                result['leave_one_source_out'] = []
                if len(included) > 1 and result['status'] != 'exact':
                    for row in included:
                        remaining = [r for r in included if r['source_id'] != row['source_id']]
                        alternative = _mean(remaining)
                        result['leave_one_source_out'].append(dict(
                            omitted_source_id=row['source_id'],
                            p_mean=alternative['p_mean'],
                            source_count=alternative['source_count']))
                result['sensitivity_alternatives'] = []
                for rule in policy.get('sensitivities', []):
                    if rule['target'] != {'q': q, 'd': d}:
                        continue
                    alternatives = [r for r in target if _matches(r, rule['alternative_match'])]
                    if len(alternatives) != 1:
                        raise ValueError('Sensitivity alternative must identify one row')
                    substitute = [r for r in included if r['source_id'] != rule['replace_source_id']]
                    substitute += alternatives
                    variant = _mean(substitute)
                    result['sensitivity_alternatives'].append(dict(
                        name=rule['name'], p_mean=variant['p_mean'],
                        source_count=variant['source_count'],
                        contributions=variant['contributions']))
                results[q, d] = result
        return results, prepared, data, policy


def calculate():
    """Return {(q,d): result}, with Decimal p_mean and explicit missing rows."""
    return _compute()[0]


def _text(value):
    if value is None:
        return ''
    if isinstance(value, D):
        return format(value, 'f')
    return str(value)


def _json_default(value):
    if isinstance(value, D):
        return _text(value)
    raise TypeError(type(value).__name__)


def _csv(rows, fields):
    output = io.StringIO()
    writer = csv.DictWriter(output, fieldnames=fields, lineterminator='\n')
    writer.writeheader()
    writer.writerows({k: _text(row.get(k)) for k in fields} for row in rows)
    return output.getvalue()


def artifact_contents():
    """Return deterministic generated paths/text; no writes or output on import."""
    results, prepared, data, policy = _compute()
    document = dict(
        method=policy['method'],
        precision_decimal_digits=policy['arithmetic_precision_decimal_digits'],
        interpretation=policy['scope'],
        input_file='data/benchmarks.json',
        input_sha256=hashlib.sha256(DATA.read_bytes()).hexdigest(),
        policy_sha256=hashlib.sha256(POLICY.read_bytes()).hexdigest(),
        researched_on=data['researched_on'],
        limitations=policy['limitations'], sources=data['sources'],
        results=list(results.values()))
    averages = [dict(q=q, d=d, status=r['status'], p_mean=r['p_mean'],
                     source_count=r['source_count'],
                     source_ids=';'.join(c['source_id'] for c in r['contributions']))
                for (q, d), r in results.items()]
    weights = []
    for row in prepared:
        result = results[row['q'], row['d']]
        contribution = next((c for c in result['contributions']
                             if c['source_id'] == row['source_id']), None)
        excluded = row.get('excluded_reason')
        superseded = result['status'] == 'exact' and (not row['exact'] or contribution is None)
        status = ('excluded' if excluded else 'superseded_by_exact' if superseded
                  else 'exact' if row['exact'] else 'included')
        reason = excluded or ('An exact result takes precedence for this target.' if superseded else '')
        weight = None if excluded or superseded or contribution is None else contribution['nominal_weight']
        normalized = D(0) if excluded or superseded or contribution is None else contribution['normalized_weight']
        weights.append(dict(q=row['q'], d=row['d'], source_id=row['source_id'],
                            status=status, original_variable=row['original_variable'],
                            original_printed=row['original_printed'],
                            original_value=row['original_value'],
                            original_uncertainty=row['original_uncertainty'],
                            p_value=row['p'], p_low=row['p_low'], p_high=row['p_high'],
                            p_error=row['u'], nominal_weight=weight,
                            normalized_weight=normalized, exclusion_reason=reason,
                            source_url=row['source_url'], source_type=row['source_type'],
                            source_location=row['source_location']))
    return {
        'literature/averages.json': json.dumps(document, indent=2, ensure_ascii=False,
                                              default=_json_default)+'\n',
        'literature/averages.csv': _csv(averages, ['q','d','status','p_mean','source_count','source_ids']),
        'literature/weights.csv': _csv(weights, ['q','d','source_id','status','original_variable',
            'original_printed','original_value','original_uncertainty','p_value','p_low','p_high',
            'p_error','nominal_weight','normalized_weight','exclusion_reason','source_url',
            'source_type','source_location'])}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    for name, content in artifact_contents().items():
        target = ROOT/name
        if args.check:
            if not target.exists() or target.read_text() != content:
                raise SystemExit('LITERATURE_REGENERATION_MISMATCH '+name)
        else:
            target.write_text(content)
    print('LITERATURE_REPRODUCTION=PASS' if args.check else 'LITERATURE_GENERATED=PASS')


if __name__ == '__main__':
    main()
