// Exact solver for the {SW, N, E} piece game (MO q/363120, MSE q/3689425).
// Board R x C, cells (x, y) with 0 <= x < C, 0 <= y < R; moves (-1,-1), (0,+1), (+1,0);
// no square may be visited twice; the player who cannot move loses.
// Output: one row per y from top (y = R-1) to bottom (y = 0); 'L' = player to move from the
// start square loses (second player wins), 'W' = first player wins.
// Usage: solve R C            (whole board)
//        solve R C x y        (one start square)
// Method: negamax with a transposition table keyed on the exact (position, visited set).
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXW 4  // up to 256 cells
typedef struct { uint64_t w[MAXW]; } Set;

static int R, C, NW;
static const int DX[3] = {-1, 0, 1}, DY[3] = {-1, 1, 0};

typedef struct { uint64_t w[MAXW]; uint16_t pos; uint8_t used, val; } Entry;
static Entry *tt;
static uint64_t ttmask;
static uint64_t zob[256][MAXW];
static long long nodes;

static uint64_t hashkey(const Set *s, int pos) {
    uint64_t h = 0x9E3779B97F4A7C15ULL * (uint64_t)(pos + 1);
    for (int i = 0; i < NW; i++) {
        uint64_t v = s->w[i] + 0x632BE59BD9B4E019ULL * (uint64_t)(i + 1);
        v ^= v >> 31; v *= 0xBF58476D1CE4E5B9ULL; v ^= v >> 29;
        h ^= v + 0x94D049BB133111EBULL + (h << 6) + (h >> 2);
    }
    return h;
}

static inline int get(const Set *s, int c) { return (s->w[c >> 6] >> (c & 63)) & 1; }
static inline void setb(Set *s, int c) { s->w[c >> 6] |= 1ULL << (c & 63); }
static inline void clrb(Set *s, int c) { s->w[c >> 6] &= ~(1ULL << (c & 63)); }


// Unvisited cells reachable from pos along legal moves, avoiding visited cells.
static void reach(const Set *s, int pos, Set *out) {
    static int stack[256];
    memset(out, 0, sizeof *out);
    int sp = 0; stack[sp++] = pos;
    while (sp) {
        int p = stack[--sp], x = p % C, y = p / C;
        for (int d = 0; d < 3; d++) {
            int nx = x + DX[d], ny = y + DY[d];
            if (nx < 0 || ny < 0 || nx >= C || ny >= R) continue;
            int c = ny * C + nx;
            if (get(s, c) || get(out, c)) continue;
            setb(out, c); stack[sp++] = c;
        }
    }
}

// returns 1 if the player to move from pos (already visited) wins
static int win(Set *s, int pos) {
    nodes++;
    int x = pos % C, y = pos / C;
    int nb[3], k = 0;
    for (int d = 0; d < 3; d++) {
        int nx = x + DX[d], ny = y + DY[d];
        if (nx < 0 || ny < 0 || nx >= C || ny >= R) continue;
        int c = ny * C + nx;
        if (!get(s, c)) nb[k++] = c;
    }
    if (k == 0) return 0;
    if (k == 1) {  // forced move: no table entry needed
        setb(s, nb[0]);
        int r = !win(s, nb[0]);
        clrb(s, nb[0]);
        return r;
    }
    // Key: the unvisited cells still reachable from pos (the future depends only on these).
    Set key; reach(s, pos, &key);
    uint64_t h = hashkey(&key, pos), i = h & ttmask;
    for (int probe = 0; probe < 8; probe++, i = (i + 1) & ttmask) {
        Entry *e = &tt[i];
        if (!e->used) break;
        if (e->pos == pos && !memcmp(e->w, key.w, sizeof(uint64_t) * NW)) return e->val;
    }
    int r = 0;
    for (int j = 0; j < k && !r; j++) {
        setb(s, nb[j]);
        if (!win(s, nb[j])) r = 1;
        clrb(s, nb[j]);
    }
    // store (replace the first slot of the probe window if full)
    i = h & ttmask;
    Entry *slot = &tt[i];
    for (int probe = 0; probe < 8; probe++) {
        Entry *e = &tt[(i + probe) & ttmask];
        if (!e->used) { slot = e; break; }
    }
    memset(slot->w, 0, sizeof slot->w);
    memcpy(slot->w, key.w, sizeof(uint64_t) * NW);
    slot->pos = (uint16_t)pos; slot->used = 1; slot->val = (uint8_t)r;
    return r;
}

static int solve_start(int x, int y) {
    Set s; memset(&s, 0, sizeof s);
    int p = y * C + x;
    setb(&s, p);
    return win(&s, p);
}

#ifndef NO_MAIN
int main(int argc, char **argv) {
    if (argc != 3 && argc != 5) { fprintf(stderr, "usage: solve R C [x y]\n"); return 2; }
    R = atoi(argv[1]); C = atoi(argv[2]);
    if (R < 1 || C < 1 || R * C > 64 * MAXW) { fprintf(stderr, "board too large\n"); return 2; }
    NW = (R * C + 63) / 64;
    int bits = 24;
    const char *tb = getenv("TTBITS"); if (tb) bits = atoi(tb);
    ttmask = (1ULL << bits) - 1;
    tt = calloc(ttmask + 1, sizeof(Entry));
    if (!tt) { fprintf(stderr, "no memory\n"); return 1; }
    (void)zob;
    if (argc == 5) {
        int x = atoi(argv[3]), y = atoi(argv[4]);
        printf("%c\n", solve_start(x, y) ? 'W' : 'L');
    } else {
        for (int y = R - 1; y >= 0; y--) {
            for (int x = 0; x < C; x++) putchar(solve_start(x, y) ? 'W' : 'L');
            putchar('\n');
            fflush(stdout);
        }
    }
    fprintf(stderr, "nodes %lld\n", nodes);
    return 0;
}
#endif
