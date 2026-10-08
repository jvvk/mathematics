// (tester copied from antisq.c) Enumerate binary shuffle anti-squares of length L (Grytczuk–Pawlik–Pleszczyński, arXiv 2308.13882, Conj. 1).
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


// Two-cut distance of anti-squares (GPP, Symmetry 15 (2023) 1982, cutting distance, Conj. 4: s(2) = 1).
// Input: anti-square necklace representatives, one per line. Every rotation T of each is an anti-square, so
// cut(T, S_2) >= 2. Cutting T = ABC (0 <= i <= j <= L) and rearranging gives ACB, BAC, CBA besides rotations;
// cut(T, S_2) = 2 iff one of these is a shuffle square. Prints any word needing 3+ cuts and, per necklace,
// "necklace max_over_rotations" where max is 2 or 3 (3 meaning ">= 3").
static int t[64];
static int build_test(const int *x, int lx, const int *y, int ly, const int *z, int lz) {
    int k = 0;
    for (int q = 0; q < lx; q++) w[k++] = x[q];
    for (int q = 0; q < ly; q++) w[k++] = y[q];
    for (int q = 0; q < lz; q++) w[k++] = z[q];
    return is_shuffle_square();
}
static int two_cuts(void) {
    for (int i = 0; i <= L; i++)
        for (int j = i; j <= L; j++) {
            const int *A = t, *B = t + i, *C = t + j; int la = i, lb = j - i, lc = L - j;
            if (build_test(A, la, C, lc, B, lb)) return 1;   // ACB
            if (build_test(B, lb, A, la, C, lc)) return 1;   // BAC
            if (build_test(C, lc, B, lb, A, la)) return 1;   // CBA
        }
    return 0;
}
int main(void) {
    char buf[128]; long long words = 0, bad = 0, necks = 0;
    while (fgets(buf, sizeof buf, stdin)) {
        int n = 0; while (buf[n] == '0' || buf[n] == '1') n++;
        if (n == 0) continue;
        L = n; N = L / 2; necks++; int mx = 2;
        for (int r = 0; r < L; r++) {
            for (int q = 0; q < L; q++) t[q] = buf[(q + r) % L] - '0';
            words++;
            if (!two_cuts()) {
                bad++; mx = 3;
                printf("NEEDS3 "); for (int q = 0; q < L; q++) putchar('0' + t[q]); putchar('\n');
            }
        }
        buf[n] = 0; printf("%s %d\n", buf, mx);
    }
    fprintf(stderr, "necklaces=%lld words=%lld needing>=3=%lld\n", necks, words, bad);
    return 0;
}
