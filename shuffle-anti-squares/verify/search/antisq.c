// Enumerate binary shuffle anti-squares of length L (Grytczuk–Pawlik–Pleszczyński, arXiv 2308.13882, Conj. 1).
// A word is a shuffle square if it splits into two identical subsequences; an anti-square is an even word
// none of whose rotations is a shuffle square. We generate all binary necklaces (FKM), keep those with an
// even number of 1s, and test every rotation. Output: each anti-square necklace representative, one per line.
// usage: antisq L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define HBITS 20
#define HSIZE (1u << HBITS)

static int L, N;               // word length, half length
static int w[64];              // current word (rotation under test)
static int a[65];              // FKM array, 1-indexed
static uint64_t hkey[HSIZE];   // memo of failed states
static uint32_t hgen[HSIZE];
static uint32_t gen = 1;
static long long n_neck = 0, n_anti = 0;

static inline uint64_t key(int i, int plen, uint64_t p) { return ((uint64_t)i << 58) ^ ((uint64_t)plen << 52) ^ p ^ 0x9e3779b97f4a7c15ULL; }
static inline uint32_t slot(uint64_t k) { k ^= k >> 33; k *= 0xff51afd7ed558ccdULL; k ^= k >> 33; return (uint32_t)(k & (HSIZE - 1)); }

static int seen_fail(uint64_t k) {
    for (uint32_t s = slot(k);; s = (s + 1) & (HSIZE - 1)) {
        if (hgen[s] != gen) return 0;
        if (hkey[s] == k) return 1;
    }
}
static void mark_fail(uint64_t k) {
    uint32_t s = slot(k);
    while (hgen[s] == gen) s = (s + 1) & (HSIZE - 1);
    hgen[s] = gen; hkey[s] = k;
}

// i: position; na: letters placed in the leading copy; p: pending queue (front = bit 0), plen its length.
static int dfs(int i, int na, uint64_t p, int plen) {
    if (i == L) return plen == 0;
    if (plen > L - i) return 0;
    uint64_t k = key(i, plen, p);
    if (seen_fail(k)) return 0;
    int c = w[i];
    if (plen > 0 && (int)(p & 1) == c && dfs(i + 1, na, p >> 1, plen - 1)) return 1;          // trailing copy matches
    if (na < N && dfs(i + 1, na + 1, p | ((uint64_t)c << plen), plen + 1)) return 1;          // leading copy extends
    mark_fail(k);
    return 0;
}

static int is_shuffle_square(void) {
    if (++gen == 0) { memset(hgen, 0, sizeof hgen); gen = 1; }
    // WLOG the first letter goes to the leading copy.
    return dfs(1, 1, (uint64_t)w[0], 1);
}

static void test_necklace(void) {
    int ones = 0;
    for (int i = 1; i <= L; i++) ones += a[i];
    if (ones & 1) return;
    n_neck++;
    for (int r = 0; r < L; r++) {
        for (int i = 0; i < L; i++) w[i] = a[1 + (i + r) % L];
        if (is_shuffle_square()) return;
    }
    n_anti++;
    for (int i = 1; i <= L; i++) putchar('0' + a[i]);
    putchar('\n');
    fflush(stdout);
}

static void fkm(int t, int p) {
    if (t > L) { if (L % p == 0) test_necklace(); return; }
    a[t] = a[t - p]; fkm(t + 1, p);
    if (a[t - p] == 0) { a[t] = 1; fkm(t + 1, t); }
}

// stdin mode: each line a binary word; prints "1 word" if it is an anti-square, else "0 word".
static void stdin_mode(void) {
    char buf[128];
    while (fgets(buf, sizeof buf, stdin)) {
        int n = 0; while (buf[n] == '0' || buf[n] == '1') n++;
        if (n == 0 || n > 62) continue;
        L = n; N = L / 2; int anti = (n % 2 == 0);
        int ones = 0; for (int i = 0; i < n; i++) ones += buf[i] - '0';
        if (ones & 1) anti = 0;
        for (int r = 0; anti && r < L; r++) {
            for (int i = 0; i < L; i++) w[i] = buf[(i + r) % L] - '0';
            if (is_shuffle_square()) anti = 0;
        }
        buf[n] = 0; printf("%d %s\n", anti, buf);
    }
}

int main(int argc, char **argv) {
    if (argc < 2) { stdin_mode(); return 0; }
    L = atoi(argv[1]); N = L / 2;
    a[0] = 0;
    fkm(1, 1);
    fprintf(stderr, "L=%d even necklaces=%lld anti-square necklaces=%lld\n", L, n_neck, n_anti);
    return 0;
}
