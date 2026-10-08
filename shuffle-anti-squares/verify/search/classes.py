"""Collapse anti-square necklaces under reversal and complement; print class count and representatives."""
import sys

def neck(s: str) -> str:
    return min(s[i:] + s[:i] for i in range(len(s)))

def canon(s: str) -> str:
    c = s.translate(str.maketrans("01", "10"))
    return min(neck(x) for x in (s, s[::-1], c, c[::-1]))

if __name__ == "__main__":
  for f in sys.argv[1:]:
      ws = [l.strip() for l in open(f) if l.strip()]
      cls = sorted({canon(w) for w in ws})
      print(f, "necklaces", len(ws), "classes", len(cls))
