// For each poset read as digraph6 (Hasse diagram) on stdin, print n, e(P), |Aut(P)|, and the digraph6 line.
// e(P): DP over down-sets. |Aut(P)|: backtracking over permutations preserving the cover relation.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 16
static int n;
static uint32_t below[MAXN];   // below[v] = bitmask of strict lower covers... closure computed separately
static int cov[MAXN][MAXN];    // cov[u][v] = 1 if u covered by v (u < v cover)
static uint32_t down[MAXN];    // strict down-set of v (transitive closure)
static int indeg[MAXN], outdeg[MAXN];
static int perm[MAXN], used[MAXN];
static long long autcount;

static void parse(const char *s) {
    if (*s == '&') s++;
    n = s[0] - 63; s++;
    memset(cov, 0, sizeof cov);
    int k = 0;
    for (int i = 0; i < n; i++)
        for (int j = 0; j < n; j++, k++) {
            int c = s[k / 6] - 63;
            if (c >> (5 - k % 6) & 1) cov[i][j] = 1;
        }
}

static void closure(void) {
    for (int v = 0; v < n; v++) { down[v] = 0; indeg[v] = outdeg[v] = 0; }
    for (int u = 0; u < n; u++)
        for (int v = 0; v < n; v++)
            if (cov[u][v]) { down[v] |= 1u << u; outdeg[u]++; indeg[v]++; }
    for (int it = 0; it < n; it++)
        for (int v = 0; v < n; v++) {
            uint32_t d = down[v];
            for (int u = 0; u < n; u++) if (d >> u & 1) d |= down[u];
            down[v] = d;
        }
}

static unsigned long long linext(void) {
    static unsigned long long dp[1u << MAXN];
    uint32_t full = (1u << n) - 1;
    memset(dp, 0, sizeof(unsigned long long) << n);
    dp[0] = 1;
    for (uint32_t S = 0; S < full; S++) {
        if (!dp[S]) continue;
        for (int v = 0; v < n; v++)
            if (!(S >> v & 1) && (down[v] & ~S) == 0) dp[S | 1u << v] += dp[S];
    }
    return dp[full];
}

static void search(int i) {
    if (i == n) { autcount++; return; }
    for (int w = 0; w < n; w++) {
        if (used[w] || indeg[w] != indeg[i] || outdeg[w] != outdeg[i]) continue;
        int ok = 1;
        for (int j = 0; j < i && ok; j++)
            if (cov[j][i] != cov[perm[j]][w] || cov[i][j] != cov[w][perm[j]]) ok = 0;
        if (!ok) continue;
        used[w] = 1; perm[i] = w;
        search(i + 1);
        used[w] = 0;
    }
}

int main(void) {
    char line[1024];
    while (fgets(line, sizeof line, stdin)) {
        if (line[0] == '>' ) continue;
        line[strcspn(line, "\n")] = 0;
        if (!line[0]) continue;
        parse(line);
        closure();
        unsigned long long e = linext();
        autcount = 0; memset(used, 0, sizeof used);
        search(0);
        printf("%d %llu %lld %s\n", n, e, autcount, line);
    }
    return 0;
}
