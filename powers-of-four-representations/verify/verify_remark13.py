"""Exact checks for the powers printed in Sándor–Yang Remark 1.3."""
from collections import Counter
from itertools import product
import json
from pathlib import Path


def powers(limit):
    answer = []
    e = 16
    while e <= limit:
        answer.append(e)
        e *= 4
    return answer


def dense_representations(a, previous):
    """Independent, exact multiplication by the membership polynomial."""
    result = [0] * len(a)
    for i, value in enumerate(previous):
        if value:
            for j in range(len(a) - i):
                if a[j]:
                    result[i + j] += value
    return result


def main():
    limit = 1_000_000
    omitted = powers(limit)
    pair_counts = Counter(map(sum, product(omitted, repeat=2)))
    triple_counts = Counter(map(sum, product(omitted, repeat=3)))
    omitted_set = set(omitted)
    m = 0
    smallest = None
    for n in range(1, limit + 1):
        m += n in omitted_set
        bound = n + 1 - 3 * m - m * m
        delta = (n + 1 - 3 * m + 3 * pair_counts[n]
                 - triple_counts[n] + triple_counts[n - 1])
        assert delta >= bound > 0, (n, delta, bound)
        smallest = delta if smallest is None else min(smallest, delta)

    dense_limit = 512
    a = [int(n not in omitted_set) for n in range(dense_limit + 1)]
    representations = [1] + [0] * dense_limit
    results = []
    for h in range(1, 11):
        representations = dense_representations(a, representations)
        if h >= 3:
            differences = [representations[n] - representations[n - 1]
                           for n in range(1, dense_limit + 1)]
            assert min(differences) > 0
            if h == 3:
                for n in range(1, dense_limit + 1):
                    m = sum(e <= n for e in omitted)
                    expected = (n + 1 - 3 * m + 3 * pair_counts[n]
                                - triple_counts[n] + triple_counts[n - 1])
                    assert differences[n - 1] == expected
            results.append({"h": h, "last_N": dense_limit,
                            "minimum_difference": min(differences)})

    # Demonstrate the transcription error with independent coefficients.
    wrong_a = [int(n % 4 != 2) for n in range(3)]
    wrong_r = [1, 0, 0]
    for _ in range(3):
        wrong_r = dense_representations(wrong_a, wrong_r)
    assert wrong_r == [1, 3, 3]

    report = {"omitted_set": "{4^(j+2): j >= 0}",
              "sparse_check_last_N": limit,
              "sparse_minimum_difference": smallest,
              "dense_checks": results,
              "wrong_progression_R3_at_0_1_2": wrong_r,
              "status": "all exact checks passed"}
    output = Path(__file__).with_name("remark13-verification.json")
    output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
