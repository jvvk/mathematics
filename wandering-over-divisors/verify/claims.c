// Oracle check of the note's theorem statements on boards (n+1)^2, n = 1..N (exact solver from solve.c).
// T1: from (k,k), k < n, the opening E (and N) loses for the first player.
// T2: from (a,0), 1 <= a <= n, n >= 2, the opening N loses for the first player.
// T3: (2,0) is L for n >= 2; (2,2) is L for n >= 3; (0,n) and (n,0) are L for n >= 2.
// Usage: claims N
#define NO_MAIN
#include "solve.c"
static int lose_after(int x, int y, int d) {  // first plays d from start (x,y); returns 1 if the mover then loses
    Set s; memset(&s, 0, sizeof s); setb(&s, y * C + x);
    int nx = x + DX[d], ny = y + DY[d];
    if (nx < 0 || ny < 0 || nx >= C || ny >= R) return -1;
    setb(&s, ny * C + nx);
    return !win(&s, ny * C + nx) ? 0 : 1;  // 1 = second player (now to move) wins
}
static int L(int x, int y) { Set s; memset(&s, 0, sizeof s); setb(&s, y * C + x); return !win(&s, y * C + x); }
int main(int argc, char **argv) {
    int N = atoi(argv[1]), bad = 0;
    for (int n = 1; n <= N; n++) {
        R = C = n + 1; NW = (R * C + 63) / 64; ttmask = (1ULL << 25) - 1;
        free(tt); tt = calloc(ttmask + 1, sizeof(Entry));
        for (int k = 0; k < n; k++) if (lose_after(k, k, 2) != 1 || lose_after(k, k, 1) != 1) { printf("T1 fails n=%d k=%d\n", n, k); bad++; }
        if (n >= 2) for (int a = 1; a <= n; a++) if (lose_after(a, 0, 1) != 1) { printf("T2 fails n=%d a=%d\n", n, a); bad++; }
        if (n >= 2 && !L(2, 0)) { printf("T3 (2,0) fails n=%d\n", n); bad++; }
        if (n >= 3 && !L(2, 2)) { printf("T3 (2,2) fails n=%d\n", n); bad++; }
        if (n >= 2 && (!L(0, n) || !L(n, 0))) { printf("T3 corner fails n=%d\n", n); bad++; }
        printf("n=%d checked\n", n); fflush(stdout);
    }
    // boundary of the ranges: T2 at n = 1, corner at n = 1, (2,2) at n = 2 should fail or be out of range
    R = C = 2; NW = 1; free(tt); tt = calloc(ttmask + 1, sizeof(Entry));
    printf("n=1: (1,0) N-opening second wins? %d (expect 0); (0,1) L? %d (expect 0)\n", lose_after(1, 0, 1), L(0, 1));
    printf("%s\n", bad ? "SOME CLAIMS FAIL" : "all claims hold");
    return 0;
}
