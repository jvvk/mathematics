"""Exact row-word checks from the original density script."""

def runs_of(S, n):
    cuts = [0] + sorted(S) + [n]
    return [cuts[i + 1] - cuts[i] for i in range(len(cuts) - 1)]

def check_word(word, S, shape):
    rows = {}
    for v, r in enumerate(word, start=1):
        rows.setdefault(r, []).append(v)
    sh = tuple(len(rows.get(i, [])) for i in range(1, max(rows) + 1))
    if sh != tuple(x for x in shape if x > 0):
        return False
    for i in range(2, len(sh) + 1):  # column strictness
        for col, v in enumerate(rows[i]):
            if col >= len(rows[i - 1]) or rows[i - 1][col] > v:
                return False
    D = {i for i in range(1, len(word)) if word[i] > word[i - 1]}
    return D == set(S)
