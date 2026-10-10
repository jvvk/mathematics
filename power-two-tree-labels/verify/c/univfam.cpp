// q/304266: compute the TRUE universal family. S (0 = min S, |S| = n, S within [0, span)) is universal if every
// rooted binary tree on n vertices embeds bijectively onto S, root -> 0, child = parent + 2^k.
// Brute force over all such S and all trees (direct backtracking, no reductions). Prints primitive universal sets
// (some element odd; all-even sets are 2 * a smaller set).
// usage: univfam nmax spanfactor   (span = spanfactor * n)
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <vector>
#include <string>
using namespace std;

struct Tree { vector<int> c1, c2; int n; };     // children of each vertex (-1 = none); vertex 0 = root; preorder
static vector<vector<Tree>> trees;              // trees[n] = all unordered rooted binary trees on n vertices

static Tree join(const Tree *a, const Tree *b) {  // new root with subtrees a (and b if non-null)
    Tree t; t.n = 1 + (a ? a->n : 0) + (b ? b->n : 0);
    t.c1.assign(1, -1); t.c2.assign(1, -1);
    auto app = [&](const Tree *s) {
        int off = (int)t.c1.size();
        for (int i = 0; i < s->n; i++) {
            t.c1.push_back(s->c1[i] < 0 ? -1 : s->c1[i] + off);
            t.c2.push_back(s->c2[i] < 0 ? -1 : s->c2[i] + off);
        }
        return off;
    };
    if (a) t.c1[0] = app(a);
    if (b) t.c2[0] = app(b);
    return t;
}

static void gen(int nmax) {
    trees.assign(nmax + 1, {});
    Tree leaf; leaf.n = 1; leaf.c1 = {-1}; leaf.c2 = {-1};
    trees[1].push_back(leaf);
    for (int n = 2; n <= nmax; n++) {
        for (auto &a : trees[n - 1]) trees[n].push_back(join(&a, nullptr));
        for (int b = 1; 2 * b <= n - 1; b++) {
            int a = n - 1 - b;
            for (size_t i = 0; i < trees[a].size(); i++)
                for (size_t j = 0; j < trees[b].size(); j++) {
                    if (a == b && j > i) continue;
                    trees[n].push_back(join(&trees[a][i], &trees[b][j]));
                }
        }
    }
}

static const Tree *T; static uint64_t S; static int lab[64];
static bool place(int v, uint64_t used);
// assign labels to vertices v, v+1, ... in preorder; parent labels already fixed when we reach a vertex
static vector<int> par;
static bool place(int v, uint64_t used) {
    if (v == T->n) return true;
    int p = lab[par[v]];
    for (int k = 0; p + (1 << k) < 64; k++) {
        int x = p + (1 << k);
        if ((S >> x & 1) && !(used >> x & 1)) {
            lab[v] = x;
            if (place(v + 1, used | (1ULL << x))) return true;
        }
    }
    return false;
}
static bool embeds(const Tree &t, uint64_t s) {
    T = &t; S = s; par.assign(t.n, -1);
    for (int i = 0; i < t.n; i++) { if (t.c1[i] >= 0) par[t.c1[i]] = i; if (t.c2[i] >= 0) par[t.c2[i]] = i; }
    lab[0] = 0;
    return place(1, 1);
}

int main(int argc, char **argv) {
    if (argc > 2 && std::string(argv[1]) == "set") {          // univfam set x0 x1 ... : is this one set universal?
        uint64_t s = 0; int n = argc - 2;
        for (int i = 2; i < argc; i++) s |= 1ULL << atoi(argv[i]);
        gen(n); long long bad = 0; int first = -1;
        for (size_t i = 0; i < trees[n].size(); i++) if (!embeds(trees[n][i], s)) { bad++; if (first < 0) first = (int)i; }
        printf("n=%d trees=%zu failing=%lld%s\n", n, trees[n].size(), bad, bad ? "" : "  UNIVERSAL");
        return 0;
    }
    if (argc > 2 && std::string(argv[1]) == "grow") {         // univfam grow nmax : exact primitive universal family
        // Primitive universal S of size n has the form {0} u (2^i + T), T primitive universal of size n-1
        // (tail lemma: S \ {0} - s_1 is universal; primitivity forces the tail unscaled), and S needs a second power
        // of two (binary root), which bounds 2^i <= max T. So candidates are finite; test each against every tree.
        int nmax = atoi(argv[2]); gen(nmax);
        vector<uint64_t> U = {1};
        printf("n=1 { 0 }\n");
        for (int n = 2; n <= nmax; n++) {
            vector<uint64_t> V; long long cand = 0;
            for (uint64_t t : U) {
                int mx = 63 - __builtin_clzll(t);
                for (int p = 1; p == 1 || p <= mx; p *= 2) {
                    if (mx + p > 63) { fprintf(stderr, "label overflow\n"); return 1; }
                    uint64_t s = 1 | (t << p);
                    bool dup = false; for (uint64_t v : V) if (v == s) dup = true;
                    if (dup) continue;
                    cand++;
                    bool ok = true;
                    for (auto &tr : trees[n]) if (!embeds(tr, s)) { ok = false; break; }
                    if (ok) V.push_back(s);
                }
            }
            U = V;
            printf("n=%d candidates=%lld universal=%zu:", n, cand, U.size());
            for (uint64_t s : U) { printf(" {"); for (int x = 0; x < 64; x++) if (s >> x & 1) printf("%s%d", x ? "," : "", x); printf("}"); }
            printf("\n"); fflush(stdout);
        }
        return 0;
    }
    int nmax = atoi(argv[1]); double f = atof(argv[2]);
    gen(nmax);
    for (int n = 1; n <= nmax; n++) {
        int span = (int)(f * n); if (span > 63) span = 63;
        long long tot = 0, uni = 0;
        // enumerate subsets of [1, span) of size n-1
        int m = span - 1, k = n - 1;
        vector<int> idx(k); for (int i = 0; i < k; i++) idx[i] = i;
        while (true) {
            uint64_t s = 1; bool odd = false;
            for (int i : idx) { s |= 1ULL << (i + 1); if ((i + 1) & 1) odd = true; }
            if (odd || n == 1) {
                tot++;
                bool ok = true;
                for (auto &t : trees[n]) if (!embeds(t, s)) { ok = false; break; }
                if (ok) {
                    uni++;
                    printf("U n=%d {", n);
                    for (int x = 0; x < 64; x++) if (s >> x & 1) printf(" %d", x);
                    printf(" }\n");
                }
            }
            int i = k - 1;
            while (i >= 0 && idx[i] == m - k + i) i--;
            if (i < 0) break;
            idx[i]++; for (int j = i + 1; j < k; j++) idx[j] = idx[j - 1] + 1;
        }
        fprintf(stderr, "n=%d trees=%zu primitive sets tested=%lld universal=%lld\n", n, trees[n].size(), tot, uni);
    }
}
