"""Find weights w >= 0, sum 1, on competitors with  sum_k w_k |Z_k|^2 >= |Z_t|^2 + margin on all samples.
(exploration, MO 442949) Usage: python avgbeat.py n p q samples"""
import sys
import numpy as np
from scipy.optimize import linprog
from hunt import all_classes, spans2

n = int(sys.argv[1]); tp = tuple(int(c) for c in sys.argv[2]); tq = tuple(int(c) for c in sys.argv[3])
N = int(sys.argv[4])
C = all_classes(n); P = np.array([c[0] for c in C]); Q = np.array([c[1] for c in C])
ti = C.index(min((tp, tq), (tp[::-1], tq[::-1])))
rng = np.random.default_rng(11); rowsD = []
for s in range(N):
    L = np.sort(rng.exponential(1, n) ** rng.uniform(0.2, 3)) + 1e-9 * np.arange(n); L = L / L.sum()
    A = np.sort(rng.exponential(1, n - 1) ** rng.uniform(0.2, 3)); A = A / A.sum() * rng.uniform(0.01, np.pi / 2)
    s2 = spans2(L, A, P, Q); rowsD.append(np.delete(s2 - s2[ti], ti))
D = np.array(rowsD); K = D.shape[1]
# maximize t s.t. D w >= t, sum w = 1, w >= 0
c = np.zeros(K + 1); c[-1] = -1
A_ub = np.hstack([-D, np.ones((N, 1))]); b_ub = np.zeros(N)
res = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=np.hstack([np.ones((1, K)), [[0]]]), b_eq=[1],
              bounds=[(0, None)] * K + [(None, None)], method="highs")
w = res.x[:K]; others = [C[i] for i in range(len(C)) if i != ti]
print("best worst-case margin", res.x[-1])
for k in np.argsort(-w)[:8]:
    if w[k] > 1e-6: print(f"  w={w[k]:.4f}", "".join(map(str, others[k][0])), "".join(map(str, others[k][1])))
