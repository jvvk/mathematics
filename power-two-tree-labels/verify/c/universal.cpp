// Exact primitive universal sets. Compact shape enumeration, independent
// bit-mask search, checked witnesses, explicit refusal of label overflow.
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <vector>
using Mask = uint64_t;
struct Shape { int a, b, size; };
std::vector<Shape> shapes;
std::vector<std::vector<int>> by_size;
int parents[64], subsize[64], labels[64], vertices;
long long tested = 0;
int flatten(int id, int parent) {
    int v = vertices++;
    parents[v] = parent; subsize[v] = shapes[id].size;
    if (shapes[id].a >= 0) flatten(shapes[id].a, v);
    if (shapes[id].b >= 0) flatten(shapes[id].b, v);
    return v;
}
bool place(int v, Mask unused) {
    if (v == vertices) return true;
    int p = labels[parents[v]];
    for (int d = 1; p + d < 64; d *= 2) {
        int x = p + d;
        Mask bit = Mask(1) << x;
        if (!(unused & bit)) continue;
        Mask larger = x == 63 ? 0 : unused >> (x + 1);
        if (__builtin_popcountll(larger) < subsize[v] - 1) continue;
        labels[v] = x;
        if (place(v + 1, unused ^ bit)) return true;
    }
    return false;
}
bool fits(int id, Mask s) {
    vertices = 0; flatten(id, -1); labels[0] = 0; ++tested;
    if (!place(1, s ^ 1)) return false;
    Mask seen = 0;
    for (int v = 0; v < vertices; ++v) {
        Mask bit = Mask(1) << labels[v];
        if (seen & bit) std::abort();
        seen |= bit;
        if (v) {
            int d = labels[v] - labels[parents[v]];
            if (d <= 0 || (d & (d - 1))) std::abort();
        }
    }
    if (seen != s) std::abort();
    return true;
}
void print_set(Mask s) {
    printf(" {"); bool first = true;
    for (int x = 0; x < 64; ++x) if ((s >> x) & 1) {
        printf("%s%d", first ? "" : ",", x); first = false;
    }
    printf("}");
}
int main(int argc, char **argv) {
    int top = argc > 1 ? atoi(argv[1]) : 20;
    if (top < 1 || top >= 64) return 2;
    by_size.resize(top + 1);
    shapes.push_back({-1, -1, 1}); by_size[1].push_back(0);
    std::vector<Mask> universal = {1};
    printf("n=1 trees=1 candidates=1 universal=1: {0}\n");
    for (int n = 2; n <= top; ++n) {
        auto add = [&](int a, int b) {
            by_size[n].push_back((int)shapes.size()); shapes.push_back({a, b, n});
        };
        for (int a : by_size[n - 1]) add(a, -1);
        for (int b = 1; b * 2 <= n - 1; ++b) {
            int a = n - 1 - b;
            for (int x : by_size[a]) for (int y : by_size[b]) {
                if (a != b || x <= y) add(x, y);
            }
        }
        std::vector<Mask> candidates, next;
        for (Mask t : universal) {
            int mx = 63 - __builtin_clzll(t);
            for (int p = 1; p == 1 || p <= mx; p *= 2) {
                if (mx + p >= 64) { fprintf(stderr, "Incomplete: label overflow\n"); return 2; }
                candidates.push_back(1 | (t << p));
            }
        }
        std::sort(candidates.begin(), candidates.end());
        candidates.erase(std::unique(candidates.begin(), candidates.end()), candidates.end());
        for (Mask s : candidates) {
            bool ok = true;
            for (int id : by_size[n]) if (!fits(id, s)) { ok = false; break; }
            if (ok) next.push_back(s);
        }
        universal = next;
        printf("n=%d trees=%zu candidates=%zu universal=%zu:", n, by_size[n].size(), candidates.size(), universal.size());
        for (Mask s : universal) print_set(s);
        printf("\n"); fflush(stdout);
    }
    fprintf(stderr, "checked %lld embeddings; all successful witnesses validated\n", tested);
}
