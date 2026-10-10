// Oracle sample for the square-weight test (Conway soldiers / pagoda style): sample random mid-game positions (first to move), compute the exact
// value and simple features of the reachable free region; print a CSV for analysis.
// Usage: features n samples seed
#define NO_MAIN
#include "../solve.c"
int main(int argc, char **argv) {
    int n = atoi(argv[1]), S = atoi(argv[2]); srand(atoi(argv[3]));
    R = C = n + 1; NW = (R * C + 63) / 64; ttmask = (1ULL << 24) - 1; tt = calloc(ttmask + 1, sizeof(Entry));
    printf("x,y,lose,outdeg,reachbits\n");
    for (int k = 0; k < S; k++) {
        Set s; memset(&s, 0, sizeof s);
        int x = rand() % C, y = rand() % R; setb(&s, y * C + x);
        int len = rand() % 12;
        for (int i = 0; i < len; i++) {
            int opt[3], c = 0;
            for (int d = 0; d < 3; d++) { int nx = x + DX[d], ny = y + DY[d];
                if (nx >= 0 && ny >= 0 && nx < C && ny < R && !get(&s, ny * C + nx)) opt[c++] = d; }
            if (!c) break;
            int d = opt[rand() % c]; x += DX[d]; y += DY[d]; setb(&s, y * C + x);
        }
        Set rs; reach(&s, y * C + x, &rs);
        int cnt = 0, c3[3] = {0}, par[4] = {0}, od = 0;
        for (int c = 0; c < R * C; c++) if (get(&rs, c)) { int cx = c % C, cy = c / C; cnt++; c3[(cx + cy) % 3]++; par[(cx & 1) + 2 * (cy & 1)]++; }
        for (int d = 0; d < 3; d++) { int nx = x + DX[d], ny = y + DY[d];
            if (nx >= 0 && ny >= 0 && nx < C && ny < R && !get(&s, ny * C + nx)) od++; }
        int lose = !win(&s, y * C + x);
        printf("%d,%d,%d,%d,", x, y, lose, od); for (int c = 0; c < R * C; c++) putchar(get(&rs, c) ? '1' : '0'); putchar('\n');
    }
    return 0;
}
