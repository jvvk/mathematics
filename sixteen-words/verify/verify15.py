"""Independent check (pure Python, no numpy) that a word list covers {0,1}^n by subsequences."""
import itertools
import sys

S16 = "0000000000 0000000011 0000111110 0011001100 0011111111 0110000110 0110101001 0111110000 1000001111 1001010110 1001111001 1100000000 1100110011 1111000001 1111111100 1111111111".split()


def is_subseq(y: str, x: str) -> bool:
    it = iter(x)
    return all(c in it for c in y)


def covers(S: list[str], n: int) -> bool:
    return all(any(is_subseq(y, "".join(x)) for y in S) for x in itertools.product("01", repeat=n))


if __name__ == "__main__":
    ok = covers(S16, 15)
    muts = [covers(S16[:i] + S16[i + 1 :], 15) for i in range(len(S16))]
    print("cover ok:", ok, "| single-deletion mutants still covering:", sum(muts), "of", len(muts))
    sys.exit(0 if ok and not any(muts) else 1)
