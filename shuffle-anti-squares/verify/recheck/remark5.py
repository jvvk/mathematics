"""Independent check of Remark 5 (shares no code with code/): a word is a shuffle square iff the empty buffer is
reachable, where buffers evolve as in He-Post (arXiv 2512.12077, Prop. 2.1): B_t = {w+c} u {w[1:] : w[0] = c}."""


def is_ss(w: str) -> bool:
    B = {""}
    n = len(w)
    for t, c in enumerate(w):
        nxt = set()
        for b in B:
            if len(b) + 1 <= n - t - 1:
                nxt.add(b + c)
            if b and b[0] == c:
                nxt.add(b[1:])
        B = nxt
    return "" in B


def some_rotation_ss(w: str) -> bool:
    return any(is_ss(w[r:] + w[:r]) for r in range(len(w)))


if __name__ == "__main__":
    assert is_ss("1100") and not is_ss("0110") and not some_rotation_ss("000001001111000011101111")
    for a, b in [(5, 7), (3, 5)]:
        bad = [K for K in range(0, 21) if not some_rotation_ss("0" * K + "1" * a + "0" * K + "1" * b)]
        print(f"0^K 1^{a} 0^K 1^{b}: K <= 20 with no shuffle-square rotation: {bad}")
