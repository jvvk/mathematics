// MO 514920: enumerate binary words of length n, fingerprint the characteristic polynomial of H_b
// (b on the diagonal, 1 on the off-diagonals) by evaluating it at two points mod 2^61-1 via the
// three-term recurrence P_k = (x - b_k) P_{k-1} - P_{k-2}, and print every fingerprint class that
// contains two or more reversal classes. Only words with b <= reverse(b) are stored.
// Mutant: -DMUT_SHORTFP truncates the fingerprint.
// Usage: enum n   ->  lines "fp_hex word word ..." (words as 0/1 strings, b_1 first).
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

typedef unsigned __int128 u128;
static const uint64_t MP = (1ULL << 61) - 1;
static inline uint64_t mulm(uint64_t a, uint64_t b) {
    u128 z = (u128)a * b;
    uint64_t lo = (uint64_t)(z & MP), hi = (uint64_t)(z >> 61);
    uint64_t s = lo + hi;
    return s >= MP ? s - MP : s;
}
static inline uint64_t subm(uint64_t a, uint64_t b) { return a >= b ? a - b : a + MP - b; }

typedef struct { uint64_t h1, h2; uint32_t w; } Rec;
static int n;
static Rec *recs;
static size_t nrec;
static const uint64_t X1 = 0x1234567890ABCDULL % ((1ULL << 61) - 1), X2 = 0x0FEDCBA987654321ULL % ((1ULL << 61) - 1);

static uint32_t rev(uint32_t w) {
    uint32_t r = 0;
    for (int i = 0; i < n; i++) r |= ((w >> i) & 1u) << (n - 1 - i);
    return r;
}

// bit i of w (i = 0 .. n-1) is b_{i+1}
static void dfs(int k, uint32_t w, uint64_t a1, uint64_t b1, uint64_t a2, uint64_t b2) {
    // a = P_k, b = P_{k-1} at the two points
    if (k == n) {
        if (w <= rev(w)) {
#ifdef MUT_SHORTFP
            a1 &= 0xFFF; a2 = 0;   // mutant: 12-bit fingerprint, forces false collisions
#endif
            recs[nrec].h1 = a1; recs[nrec].h2 = a2; recs[nrec].w = w; nrec++;
        }
        return;
    }
    for (uint32_t bit = 0; bit < 2; bit++) {
        uint64_t c1 = subm(mulm(subm(X1, bit), a1), b1);
        uint64_t c2 = subm(mulm(subm(X2, bit), a2), b2);
        dfs(k + 1, w | (bit << k), c1, a1, c2, a2);
    }
}

static int cmp(const void *x, const void *y) {
    const Rec *a = x, *b = y;
    if (a->h1 != b->h1) return a->h1 < b->h1 ? -1 : 1;
    if (a->h2 != b->h2) return a->h2 < b->h2 ? -1 : 1;
    return a->w < b->w ? -1 : a->w > b->w;
}

int main(int argc, char **argv) {
    n = atoi(argv[1]);
    recs = malloc(sizeof(Rec) * ((1ULL << (n - 1)) + (1ULL << (n / 2 + 1))));
    dfs(0, 0, 1, 0, 1, 0);
    qsort(recs, nrec, sizeof(Rec), cmp);
    size_t classes = 0;
    for (size_t i = 0; i < nrec;) {
        size_t j = i;
        while (j < nrec && recs[j].h1 == recs[i].h1 && recs[j].h2 == recs[i].h2) j++;
        classes++;
        if (j - i > 1) {
            printf("%016llx", (unsigned long long)recs[i].h1);
            for (size_t t = i; t < j; t++) {
                putchar(' ');
                for (int b = 0; b < n; b++) putchar('0' + ((recs[t].w >> b) & 1));
            }
            putchar('\n');
        }
        i = j;
    }
    fprintf(stderr, "n=%d reversal_classes=%zu a_n=%zu\n", n, nrec, classes);
    return 0;
}
