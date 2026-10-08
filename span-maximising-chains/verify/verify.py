"""Reproduce the exact certificates and audit the stronger sweep algorithm.

python3 verify.py --audit --exhaustive-n7 --report verification-report.json
Uses only the Python standard library. No random search is needed to verify
the claimed lower bounds; each input is supplied as exact integer data.
"""
import argparse
from fractions import Fraction
from hashlib import sha256
from itertools import permutations
import json
from math import atan, lcm, tan
from pathlib import Path
import random

from certificate import certify, certify_all_permutations, score
from solver import patterns, conjectured_patterns
from sweep import maximize_exact, integer_directions, valley_representatives


ROOT = Path(__file__).resolve().parent


def require(condition,message):
    if not condition:
        raise AssertionError(message)


def unrestricted_maximum(lengths,tangents,denominator):
    n = len(lengths)
    common = None
    ps = [(p,[lengths[j] for j in p]) for p in permutations(range(n)) if p[0] < p[-1]]
    best,count = None,0
    for q in permutations(range(n-1)):
        common,rs,ss = integer_directions(tangents,denominator,q)
        for _,ls in ps:
            x = sum(l*r for l,r in zip(ls,rs))
            y = sum(l*s for l,s in zip(ls,ss))
            v = x*x+y*y
            if best is None or v > best:
                best = v
            count += 1
    return Fraction(best,common**2),count


def verify_witnesses():
    summary = []
    expected = {4:3,5:6,6:14,7:31,8:70}
    for n,count in expected.items():
        path = ROOT/f'exact-witnesses-{n}.json'
        rows = json.loads(path.read_text())
        found = set()
        for row in rows:
            p,q,margin = certify(row['lengths'],row['tangent_numerators'],row['tangent_denominator'])
            require((list(p),list(q)) == (row['p'],row['q']),'Stored winning order differs.')
            require(margin == Fraction(row['squared_distance_margin']),'Stored margin differs.')
            value,fp,fq = maximize_exact(row['lengths'],row['tangent_numerators'],row['tangent_denominator'])
            require((fp,fq) == (p,q),'Sweep and structured enumeration differ.')
            found.add((p,q))
        require(len(rows) == len(found) == count,'Witness count or uniqueness differs.')
        require(found == set(conjectured_patterns(n)),'Observed family and recursive family differ.')
        summary.append(dict(n=n,distinct_strict_optimizers=count,
                            structured_candidates_per_witness=len(list(patterns(n))),
                            sweep_turn_orders_per_witness=len(list(valley_representatives(n))),
                            file_sha256=sha256(path.read_bytes()).hexdigest()))
        print(f'Exact witnesses verified: n={n}, {count} distinct patterns.',flush=True)
    return summary


def audit_sweep():
    rng = random.Random(4429492026)
    cases = []
    for n in range(3,7):
        for target in [.8,1.5,2.4,3.05]:
            lengths = sorted(rng.sample(range(1,1000),n))
            while True:
                weights = sorted(rng.uniform(.2,1) for _ in range(n-1))
                angles = [target*w/sum(weights) for w in weights]
                ts = [round(1000*tan(a/2)) for a in angles]
                if len(set(ts)) == len(ts) and min(ts) > 0:
                    break
            cases.append((f'n={n},target={target}',lengths,ts,1000))
    # Integer multiples of a common turn create simultaneous midpoint events.
    for n,base in [(5,Fraction(1,20)),(6,Fraction(1,10))]:
        ts,cur = [],Fraction(0)
        for _ in range(n-1):
            cur = (cur+base)/(1-cur*base)
            ts.append(cur)
        denominator = lcm(*(x.denominator for x in ts))
        nums = [int(x*denominator) for x in ts]
        cases.append((f'n={n},simultaneous-events',list(range(1,n+1)),nums,denominator))
    report = []
    for name,ls,ts,d in cases:
        fast,p,q = maximize_exact(ls,ts,d)
        full,count = unrestricted_maximum(ls,ts,d)
        require(fast == full,f'Unrestricted audit failed: {name}')
        require(p[0] == 0 and p[-1] == 1,f'Endpoint theorem failed: {name}')
        report.append(dict(case=name,unrestricted_arrangements_checked=count,
                           approximate_total_turn=sum(2*atan(t/d) for t in ts),
                           exact_objective_agreement=True))
        print(f'Unrestricted audit passed: {name}; {count} arrangements.',flush=True)
    # Exercise exact event ordering across the lower half of the complex plane,
    # and make invalid inputs fail rather than silently wrap around the circle.
    for ls,ts,d in [([1,2,3],[1000,2000],1000),([1,2,3],[1,1],10)]:
        try:
            maximize_exact(ls,ts,d)
        except ValueError:
            pass
        else:
            raise AssertionError('Invalid input accepted.')
    return report


def verify_new_n7():
    rows = json.loads((ROOT/'new-n7-witnesses.json').read_text())
    result = []
    for row in rows:
        p,q,margin,count = certify_all_permutations(row['lengths'],row['tangent_numerators'],row['tangent_denominator'])
        require(list(p) == row['p'] and list(q) == row['q'],'Exhaustive winner differs.')
        require(margin == Fraction(row['squared_distance_margin']),'Exhaustive margin differs.')
        require(count == row['arrangements_checked'] == 1814400,'Exhaustive count differs.')
        result.append(dict(p=p,q=q,arrangements_checked=count,exact_margin=str(margin)))
        print(f'All n=7 arrangements verified: {p}, {q}; {count} arrangements.',flush=True)
    return result


def verify_short_examples():
    result = []
    rows = json.loads((ROOT/'short-n4-witnesses.json').read_text())
    for row in rows:
        ls,ts,d = row['lengths'],row['tangent_numerators'],row['tangent_denominator']
        # Also checks the hypotheses needed for the counting theorem.
        certify(ls,ts,d)
        p,q,margin,count = certify_all_permutations(ls,ts,d)
        require(list(p) == row['p'] and list(q) == row['q'],'Short n=4 winner differs.')
        require(margin == Fraction(row['squared_distance_margin']),'Short n=4 margin differs.')
        require(count == row['arrangements_checked'] == 72,'Short n=4 count differs.')
        result.append(dict(p=p,q=q,arrangements_checked=count,exact_margin=str(margin)))
    # Beyond-semicircle counterexample: unrestricted evaluation only.
    values = []
    for p in permutations(range(3)):
        if p[0] < p[-1]:
            for q in permutations(range(2)):
                v,common,_,_ = score([1,2,3],[3,4],1,p,q)
                values.append((Fraction(v,common**2),p,q))
    values.sort()
    require([v for v,_,_ in values] == [Fraction(v,85) for v in [26,68,234,290,900,914]],
            'Beyond-semicircle squared spans differ.')
    require(values[-1][1:] == ((1,0,2),(1,0)),'Beyond-semicircle winner differs.')
    print('Short n=4 witnesses and beyond-semicircle example verified.',flush=True)
    return dict(short_n4_unrestricted_certificates=result,
                beyond_semicircle_example=dict(squared_spans=[str(v) for v,_,_ in values],
                                              winning_p=values[-1][1],winning_q=values[-1][2]))


def verify_recursive_constructions():
    rows = json.loads((ROOT/'constructed-witnesses.json').read_text())
    expected = {4:3,5:6,6:14,7:31,8:70,9:157,10:3,11:3,12:3}
    report = []
    for n,count in expected.items():
        selected = [row for row in rows if len(row['p']) == n]
        found = set()
        for row in selected:
            ls,ts,d = row['lengths'],row['tangent_numerators'],row['tangent_denominator']
            p,q,margin = certify(ls,ts,d)
            require((list(p),list(q)) == (row['p'],row['q']),'Constructed winner differs.')
            require(margin == Fraction(row['squared_distance_margin']),'Constructed margin differs.')
            require(Fraction(2*sum(ts),d) == Fraction(row['rational_total_turn_upper_bound']),
                    'Constructed rational turn bound differs.')
            require(Fraction(2*sum(ts),d) < Fraction(1,2),'Constructed turn bound is too large.')
            _,fp,fq = maximize_exact(ls,ts,d)
            require((fp,fq) == (p,q),'Constructed sweep and enumeration differ.')
            found.add((p,q))
        family = set(conjectured_patterns(n))
        require(len(selected) == len(found) == count,'Construction count differs.')
        require(found <= family,'Construction outside the defined recursive family.')
        if n <= 9:
            require(found == family,'Not every recursive member was constructed.')
        report.append(dict(n=n,constructed_strict_optimizers=count,entire_family=(n<=9)))
        print(f'Recursive construction certificates verified: n={n}, {count} patterns.',flush=True)
    path = ROOT/'research/non-inheriting-core.json'
    data = json.loads(path.read_text())
    row = data['whole_witness']
    p,q,margin,count = certify_all_permutations(row['lengths'],row['tangent_numerators'],row['tangent_denominator'])
    require((list(p),list(q)) == (row['p'],row['q']),'Deletion-example whole optimum differs.')
    require(margin == Fraction(data['whole_unrestricted_margin']),'Deletion-example whole margin differs.')
    require(count == data['whole_unrestricted_arrangements_checked'] == 1440,'Deletion whole count differs.')
    ls,ts,d = data['core_lengths'],data['core_tangent_numerators'],data['denominator']
    p,q,margin,count = certify_all_permutations(ls,ts,d)
    require((list(p),list(q)) == (data['bare_core_optimum']['p'],data['bare_core_optimum']['q']),
            'Deletion-example bare optimum differs.')
    require(margin == Fraction(data['bare_core_unrestricted_margin']),'Deletion bare margin differs.')
    require(count == data['bare_core_unrestricted_arrangements_checked'] == 72,'Deletion bare count differs.')
    vp,common,_,_ = score(ls,ts,d,data['recursive_parent']['p'],data['recursive_parent']['q'])
    vb,_,_,_ = score(ls,ts,d,p,q)
    improvement = Fraction(vb-vp,common**2)
    require(improvement > 0 and improvement == Fraction(data['bare_core_improvement_over_inherited_order']),
            'Bare-core improvement differs.')
    print('Failure of bare-core inheritance verified by unrestricted enumeration.',flush=True)
    return dict(constructions=report,construction_file_sha256=sha256((ROOT/'constructed-witnesses.json').read_bytes()).hexdigest(),
                bare_core_inheritance_counterexample=dict(whole_classes=1440,core_classes=72,exact_improvement=str(improvement)))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--audit',action='store_true')
    parser.add_argument('--exhaustive-n7',action='store_true')
    parser.add_argument('--recursive',action='store_true')
    parser.add_argument('--report',type=Path)
    args = parser.parse_args()
    report = dict(witnesses=verify_witnesses(),short_examples=verify_short_examples())
    if args.audit:
        report['unrestricted_sweep_audit'] = audit_sweep()
    if args.exhaustive_n7:
        report['new_n7_unrestricted_certificates'] = verify_new_n7()
    if args.recursive:
        report['recursive_realization_checks'] = verify_recursive_constructions()
    report['all_requested_checks_passed'] = True
    if args.report:
        args.report.write_text(json.dumps(report,indent=2)+'\n')


if __name__ == '__main__':
    main()
