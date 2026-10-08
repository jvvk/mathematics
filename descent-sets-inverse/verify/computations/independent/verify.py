"""Independent checks of search.cpp and the singleton-descent construction.

Run after: ./search 8 pairs counts8.txt
Python uses arbitrary-size integers. It checks the entire n=8 pair-count
matrix against permutations, and alternating maxima against the separately
proved Stanley cycle-number identity. No finite result implies a conjecture
for every n.
"""
import itertools
import json
import math
from collections import Counter, defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent


def desc(w):
    return {i + 1 for i in range(len(w) - 1) if w[i] > w[i + 1]}


def inverse(w):
    v = [0] * len(w)
    for i, x in enumerate(w, 1):
        v[x - 1] = i
    return v


def mask(s):
    return sum(1 << (i - 1) for i in s)


def singleton_witness(n, a, T):
    k = len(T)
    assert T and not (T & {t + 1 for t in T})
    assert k <= a <= n - k
    starts = {t + 1 for t in T}
    fillers = sorted(set(range(1, n + 1)) - T - starts)
    A = starts | set(fillers[:a - k])
    return sorted(A) + sorted(set(range(1, n + 1)) - A)


def singleton_formula(n, a, T):
    if not T or T & {t + 1 for t in T}:
        return 0
    t = sorted(T)
    ranges = [range(t[0])]
    ranges += [range(1, y - x) for x, y in zip(t, t[1:])]
    ranges += [range(1, n - t[-1] + 1)]
    coefficients = [1]
    for choices in ranges:
        nxt = [0] * (len(coefficients) + max(choices))
        for i, c in enumerate(coefficients):
            for j in choices:
                nxt[i + j] += c
        coefficients = nxt
    return coefficients[a] if a < len(coefficients) else 0


def verify_cpp_counts():
    cv = defaultdict(dict)
    for line in (HERE / 'counts8.txt').read_text().splitlines():
        s, shape, c = line.split()
        cv[int(s)][tuple(map(int, shape.rstrip(',').split(',')))] = int(c)
    actual = Counter()
    for w in itertools.permutations(range(1, 9)):
        actual[mask(desc(w)), mask(desc(inverse(w)))] += 1
    for s in range(128):
        for t in range(128):
            value = sum(c * cv[t].get(sh, 0) for sh, c in cv[s].items())
            assert value == actual[s, t], (s, t, value, actual[s, t])
            if s.bit_count() == 1:
                a = s.bit_length()
                T = {i + 1 for i in range(7) if t >> i & 1}
                assert value == singleton_formula(8, a, T)
    return {'n': 8, 'pair_counts_compared_with_permutations': 128**2}


def euler_numbers(N):
    row = [1]
    out = [1]
    for n in range(1, N + 1):
        nxt = [0]
        for k in range(1, n + 1):
            nxt.append(nxt[-1] + row[n - k])
        row = nxt
        out.append(row[-1])
    return out


def alternating_count(N):
    E = euler_numbers(N)
    arrays = []
    for all_cycles in (0, 1):
        C = [[0] * (N + 1) for _ in range(N + 1)]
        C[0][0] = 1
        if N:
            C[1][1] = 1
        for n in range(N - 1):
            for m in range(N + 1):
                C[n + 2][m] = ((C[n + 1][m - 1] if m else 0)
                              + (n + 1) * (n + all_cycles) * C[n][m])
        arrays.append(C)
    total = sum(E[m]**2 * arrays[int(m % 2 == 0)][N][m]
                for m in range(N + 1))
    assert total % math.factorial(N) == 0
    return total // math.factorial(N)


def verify_saved_maxima():
    out = []
    for n in range(1, 21):
        path = HERE / f'n{n}.json'
        if not path.exists():
            continue
        record = json.loads(path.read_text())
        g = alternating_count(n)
        assert record['maximum'] == record['alternating_value'] == g
        alt = sum(1 << i for i in range(0, n - 1, 2))
        alternating_masks = {alt, ((1 << (n - 1)) - 1) ^ alt}
        if n >= 4:
            assert set(record['maximisers']) == alternating_masks
        else:
            assert alternating_masks <= set(record['maximisers'])
        assert record['f'] == record['criterion_count']
        assert record['ordered_pairs_checked'] == 4**(n - 1)
        out.append({'n': n, 'g_from_cycle_identity': g})
    return out


def verify_majorization_records():
    out = []
    for path in sorted(HERE.glob('majorization*.json')):
        record = json.loads(path.read_text())
        n = record['n']
        g = alternating_count(n)
        assert record['maximum'] == record['alternating_value'] == g
        assert record['weak_majorization_failure'] == -1
        alt = sum(1 << i for i in range(0, n - 1, 2))
        assert set(record['maximisers']) == {alt, ((1 << (n - 1)) - 1) ^ alt}
        out.append({'n': n, 'g_from_cycle_identity': g,
                    'weak_majorization_failures': 0})
    return out


def verify_singletons():
    checked = 0
    for n in range(2, 17):
        for t in range(1, 1 << (n - 1)):
            if t & (t << 1):
                continue
            T = {i + 1 for i in range(n - 1) if t >> i & 1}
            k = len(T)
            for a in range(k, n - k + 1):
                w = singleton_witness(n, a, T)
                assert desc(w) == {a}
                assert desc(inverse(w)) == T
                checked += 1
    return {'constructed_permutations_checked': checked, 'maximum_n': 16}


def verify_matrix_witnesses():
    report = json.loads((HERE / 'matrix_results.json').read_text())
    retry_record = json.loads((HERE / 'matrix_retry.json').read_text())
    retries = retry_record.get('retries', [retry_record])
    checked = []
    timeouts = 0
    for c in report['cases']:
        if c['result'] == 'unknown':
            timeouts += 1
            matching = [r for r in retries
                        if (c['alpha'], c['beta']) == (r['alpha'], r['beta'])]
            assert len(matching) == 1
            retry = matching[0]
            assert retry['retry_result'] == 'sat'
            w = retry['permutation_witness']
        else:
            assert c['result'] == 'sat'
            w = c['permutation_witness']
        n = c['n']
        assert sorted(w) == list(range(1, n + 1))
        def boundaries(a):
            total = 0; cuts = set()
            for x in a[:-1]:
                total += x
                cuts.add(total)
            return cuts
        assert desc(w) == boundaries(c['alpha'])
        assert desc(inverse(w)) == boundaries(c['beta'])
        checked.append(n)
    return {'verified_permutation_witnesses': len(checked),
            'minimum_n': min(checked), 'maximum_n': max(checked),
            'initial_timeouts': timeouts, 'timeouts_resolved_on_retry': timeouts}


if __name__ == '__main__':
    report = {'cpp_independent_cross_check': verify_cpp_counts(),
              'alternating_cycle_identity_cross_check': verify_saved_maxima(),
              'majorization_cycle_identity_cross_check': verify_majorization_records(),
              'matrix_witnesses': verify_matrix_witnesses(),
              'singleton_construction': verify_singletons()}
    print(json.dumps(report, indent=2))
