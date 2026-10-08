// Independent recheck (shares no code with code/antisq.c or code/cutdist.c).
// For even length n: enumerate binary necklaces iteratively (Ruskey's successor rule), keep those with an even
// number of ones, decide which are shuffle anti-squares (no rotation is a shuffle square), and for every rotation
// of every anti-square decide whether two cuts suffice (rearrangements XZY, YXZ, ZYX of T = XYZ).
// Output: one line per anti-square necklace "word two_cut_ok(0/1)"; summary on stderr.
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <vector>

static int n;
static std::vector<int> word;

// Memo of failed states of a search over (position, queue contents). Open addressing, cleared by epoch.
struct Memo {
  std::vector<uint64_t> keys; std::vector<uint32_t> ep; uint32_t cur = 1; uint64_t mask;
  explicit Memo(int bits) : keys(1ull << bits), ep(1ull << bits, 0), mask((1ull << bits) - 1) {}
  void reset() { if (++cur == 0) { std::fill(ep.begin(), ep.end(), 0); cur = 1; } }
  static uint64_t mix(uint64_t x) { x += 0x9e3779b97f4a7c15ull; x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ull;
                                    x = (x ^ (x >> 27)) * 0x94d049bb133111ebull; return x ^ (x >> 31); }
  bool has(uint64_t k) const { for (uint64_t s = mix(k) & mask;; s = (s + 1) & mask) {
      if (ep[s] != cur) return false; if (keys[s] == k) return true; } }
  void put(uint64_t k) { uint64_t s = mix(k) & mask; while (ep[s] == cur) s = (s + 1) & mask; ep[s] = cur; keys[s] = k; }
};
static Memo memo(21);

// q holds the letters read by the leading copy but not yet by the trailing one; q's oldest letter is bit (qlen-1).
static bool ss_from(const int* w, int len, int i, int qlen, uint64_t q, int lead) {
  if (i == len) return qlen == 0;
  if (qlen > len - i) return false;
  uint64_t key = ((uint64_t)i << 40) | ((uint64_t)qlen << 34) | q;
  if (memo.has(key)) return false;
  int c = w[i];
  if (qlen > 0 && (int)((q >> (qlen - 1)) & 1) == c) {
    uint64_t q2 = q & ((1ull << (qlen - 1)) - 1);
    if (ss_from(w, len, i + 1, qlen - 1, q2, lead)) return true;
  }
  if (lead < len / 2 && ss_from(w, len, i + 1, qlen + 1, (q << 1) | (uint64_t)c, lead + 1)) return true;
  memo.put(key);
  return false;
}

static bool is_ss(const int* w, int len) {
  memo.reset();
  return ss_from(w, len, 0, 0, 0, 0);
}

static bool two_cuts_ok(const std::vector<int>& t) {
  std::vector<int> buf(n);
  for (int i = 0; i <= n; i++)
    for (int j = i; j <= n; j++) {
      // pieces X = t[0,i), Y = t[i,j), Z = t[j,n)
      const int orders[3][3] = {{0, 2, 1}, {1, 0, 2}, {2, 1, 0}};
      int start[3] = {0, i, j}, stop[3] = {i, j, n};
      for (auto& o : orders) {
        int k = 0;
        for (int p = 0; p < 3; p++) for (int x = start[o[p]]; x < stop[o[p]]; x++) buf[k++] = t[x];
        if (is_ss(buf.data(), n)) return true;
      }
    }
  return false;
}

int main(int argc, char** argv) {
  n = atoi(argv[1]);
  std::vector<int> a(n + 1, 0);
  long long even = 0, anti = 0, bad = 0;
  std::vector<int> rot(n);
  auto visit = [&]() {
    int ones = 0; for (int i = 1; i <= n; i++) ones += a[i];
    if (ones % 2) return;
    even++;
    for (int r = 0; r < n; r++) {
      for (int i = 0; i < n; i++) rot[i] = a[1 + (r + i) % n];
      if (is_ss(rot.data(), n)) return;
    }
    anti++;
    bool ok = true;
    for (int r = 0; r < n && ok; r++) {
      std::vector<int> t(n);
      for (int i = 0; i < n; i++) t[i] = a[1 + (r + i) % n];
      if (!two_cuts_ok(t)) { ok = false; bad++; }
    }
    for (int i = 1; i <= n; i++) putchar('0' + a[i]);
    printf(" %d\n", ok ? 1 : 0);
    fflush(stdout);
  };
  // iterative necklace successor: a[1..n] runs through prenecklaces; a necklace when n % p == 0
  visit();  // 0^n
  int i = n;
  while (true) {
    while (i > 0 && a[i] == 1) i--;
    if (i == 0) break;
    a[i] = 1;
    for (int j = 1; j <= n - i; j++) a[i + j] = a[j];
    if (n % i == 0) visit();
    i = n;
  }
  fprintf(stderr, "n=%d even_necklaces=%lld anti_square_necklaces=%lld needing_3_cuts=%lld\n", n, even, anti, bad);
  return 0;
}
