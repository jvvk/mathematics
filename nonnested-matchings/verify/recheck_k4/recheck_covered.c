// Independent P26 check (Fable). Usage: p26 g1 [maxgap] [maxmargin]  -> lines to stdout
// For each covered s=16 config (c1=lm+1, gaps g1,g2, right margin rm, S = 16-subset of the union of short stars),
// NN4-free, not handled by E*/mirror E*/M (a,b taken from S): find a good star.
// Output per leftover config: g1 g2 lm rm S-as-omitted-indices  firstNearGood(or 0)  firstAnyGood(or 0)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef struct { int u, v; } E;
static int compat(E a, E b) { // disjoint and non-nested
    if (a.u == b.u || a.u == b.v || a.v == b.u || a.v == b.v) return 0;
    if (a.u < b.u && b.v < a.v) return 0;
    if (b.u < a.u && a.v < b.v) return 0;
    return 1;
}
static int nnk(E *es, int m, int k, E *M, int d, int start) {
    if (d == k) return 1;
    for (int j = start; j < m; j++) {
        int ok = 1;
        for (int t = 0; t < d; t++) if (!compat(es[j], M[t])) { ok = 0; break; }
        if (!ok) continue;
        M[d] = es[j];
        if (nnk(es, m, k, M, d + 1, j + 1)) return 1;
    }
    return 0;
}
static int has(E *S, int m, int u, int v) { for (int j = 0; j < m; j++) if (S[j].u == u && S[j].v == v) return 1; return 0; }
static int lemma(E *S, int m, int n) { // 1 E*, 2 mirror E*, 3 M, 0 none
    E M[4], T[16];
    for (int c = 1; c <= n; c++) {
        if (c >= 4 && c + 2 <= n && has(S, m, c - 3, c) && has(S, m, c - 2, c) && has(S, m, c, c + 2)) {
            int t = 0; for (int j = 0; j < m; j++) if (S[j].u >= c + 4) T[t++] = S[j];
            if (nnk(T, t, 2, M, 0, 0)) return 1;
        }
        if (c >= 3 && c + 3 <= n && has(S, m, c, c + 3) && has(S, m, c, c + 2) && has(S, m, c - 2, c)) {
            int t = 0; for (int j = 0; j < m; j++) if (S[j].v <= c - 4) T[t++] = S[j];
            if (nnk(T, t, 2, M, 0, 0)) return 2;
        }
        if (c >= 4 && c + 3 <= n && has(S, m, c - 3, c) && has(S, m, c, c + 3)) {
            int a = 0, b = 0;
            for (int j = 0; j < m; j++) { if (S[j].v <= c - 4) a = 1; if (S[j].u >= c + 4) b = 1; }
            if (a && b) return 3;
        }
    }
    return 0;
}
static long ntrip = 0;
static int good(E *S, int n, int i) {
    int out[64], no = 0;
    for (int v = i + 4; v <= n; v++) out[no++] = v;
    for (int v = 1; v < i; v++) out[no++] = v;
    E es[24], M[4];
    for (int a = 0; a < no; a++) for (int b = a + 1; b < no; b++) for (int c = b + 1; c < no; c++) {
        int p = out[a], q = out[b], r = out[c];
        int st[6][2] = {{i + 1, p}, {i + 2, q}, {i + 3, r}, {p, i}, {q, i + 1}, {r, i + 2}};
        int m = 0;
        for (int k = 0; k < 6; k++) {
            int u = st[k][0], v = st[k][1]; if (u > v) { int t = u; u = v; v = t; }
            if (v - u >= 4) { es[m].u = u; es[m].v = v; m++; }   // short star edges in S are already in S
        }
        for (int j = 0; j < 16; j++) es[m++] = S[j];
        ntrip++;
        if (!nnk(es, m, 4, M, 0, 0)) return 0;
    }
    return 1;
}
int main(int argc, char **argv) {
    int G1 = atoi(argv[1]); int MG = argc > 2 ? atoi(argv[2]) : 16; int MM = argc > 3 ? atoi(argv[3]) : 10;
    long tot16 = 0, nnfree = 0, cov[4] = {0, 0, 0, 0}, left = 0, nonear = 0, nogood = 0;
    for (int g2 = 1; g2 <= MG; g2++) for (int lm = 0; lm <= MM; lm++) for (int rm = 0; rm <= MM; rm++) {
        int C[3] = {lm + 1, lm + 1 + G1, lm + 1 + G1 + g2}; int n = C[2] + rm;
        E full[18]; int m = 0;
        for (int u = 1; u <= n; u++) for (int v = u + 1; v <= n && v <= u + 3; v++) {
            int in = 0; for (int k = 0; k < 3; k++) if (u == C[k] || v == C[k]) in = 1;
            if (in) { full[m].u = u; full[m].v = v; m++; }
        }
        if (m < 16) continue;
        int q = m - 16;
        for (int o1 = 0; o1 < (q >= 1 ? m : 1); o1++) for (int o2 = (q >= 2 ? o1 + 1 : 0); o2 < (q >= 2 ? m : 1); o2++) {
            E S[16], M[4]; int t = 0;
            for (int j = 0; j < m; j++) { if (q >= 1 && j == o1) continue; if (q >= 2 && j == o2) continue; S[t++] = full[j]; }
            if (t != 16) { fprintf(stderr, "bug\n"); return 1; }
            tot16++;
            if (nnk(S, 16, 4, M, 0, 0)) continue;
            nnfree++;
            int L = lemma(S, 16, n); cov[L]++;
            if (L) continue;
            left++;
            int near = 0, any = 0;
            for (int i = 1; i <= n - 3 && !near; i++) {
                int nc = 0; for (int k = 0; k < 3; k++) if (C[k] - 3 <= i && i <= C[k]) nc = 1;
                if (nc && good(S, n, i)) near = i;
            }
            any = near;
            if (!near) { nonear++; for (int i = 1; i <= n - 3 && !any; i++) if (good(S, n, i)) any = i; if (!any) nogood++; }
            printf("%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\n", G1, g2, lm, rm, q >= 1 ? o1 : -1, q >= 2 ? o2 : -1, n, near, any);
        }
    }
    fprintf(stderr, "g1=%d subsets16=%ld nn4free=%ld E*=%ld mirE*=%ld M=%ld left=%ld no_near_good=%ld no_good=%ld triples=%ld\n",
            G1, tot16, nnfree, cov[1], cov[2], cov[3], left, nonear, nogood, ntrip);
    return 0;
}
