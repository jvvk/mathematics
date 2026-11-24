"""Integer-arithmetic exhaustive scan; all probabilities share denominator n**n."""
import argparse
import json
from fractions import Fraction
from math import comb
from pathlib import Path


def data(n, m):
    q = n - m
    w = [q**n]
    for j in range(n):
        w.append(w[-1] * (n-j) * m // ((j+1)*q))
    assert sum(w) == n**n
    lo, hi = sum(w[:m]), sum(w[m+1:])
    a, s = [], []
    total = 0
    for i in range(1, m+1):
        a.append(lo-hi)
        total += a[-1]
        s.append(total)
        lo -= w[m-i]
        hi -= w[m+i]
    assert s[-1] == sum((j-2*m)*w[j] for j in range(2*m+1, n+1))
    return w, a, s


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--max-n', type=int, default=400)
    args = p.parse_args()
    bad, multichange, reverse, examples = [], [], [], []
    minima = {}
    pairs = triples = 0
    def record(key, numerator, denominator, location):
        if key not in minima or numerator*minima[key][1] < minima[key][0]*denominator:
            minima[key] = (numerator, denominator, location)
    for n in range(2, args.max_n+1):
        for m in range(1, n//2+1):
            pairs += 1
            w, a, s = data(n, m)
            signs = [1 if x > 0 else -1 for x in a if x]
            changes = sum(x != y for x, y in zip(signs, signs[1:]))
            if changes > 1:
                multichange.append([n, m, changes])
            if any(x < y for x, y in zip(signs, signs[1:])):
                reverse.append([n, m])
            for k, value in enumerate(s, 1):
                triples += 1
                if value < 0:
                    bad.append([n, m, k])
                if n > 2*m:
                    record('S_k / P(X=m)', value, w[m], [n,m,k])
                    record('S_k / min(S_1,S_m)', value, min(s[0],s[-1]), [n,m,k])
                    if 1 < k < m:
                        record('interior S_k / min(S_1,S_m)', value, min(s[0],s[-1]), [n,m,k])
            if (n,m) in [(7,3),(9,4),(10,3),(20,9),(30,10)]:
                examples.append({'n':n,'m':m,'alpha':[str(Fraction(x,n**n)) for x in a], 'S':[str(Fraction(x,n**n)) for x in s]})
    result = {'max_n':args.max_n,'pairs':pairs,'triples':triples,'negative_S':bad,
              'alpha_more_than_one_sign_change':multichange,'alpha_negative_to_positive':reverse,
              'minima':{key:{'exact':str(Fraction(a,b)),'float':float(Fraction(a,b)),'at':loc} for key,(a,b,loc) in minima.items()},
              'examples':examples}
    path = Path(__file__).with_name('exact_scan_results.json')
    path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k != 'examples'},indent=2))
    if bad or multichange or reverse:
        raise SystemExit('FAILED: a negative partial sum or a second sign change')
    print('PASS: no negative S_k and at most one sign change (+ to -) for every n <= %d' % args.max_n)
    for x in examples:
        print(json.dumps(x))


if __name__ == '__main__':
    main()
