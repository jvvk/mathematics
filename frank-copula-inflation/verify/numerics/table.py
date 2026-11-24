"""Least number of categories m*(rho_S) at which some ordinal discretisation inflates correlation; figure data."""
import numpy as np, warnings
warnings.filterwarnings("ignore")
from scipy import optimize
from intscores import best, rho_s
from regression import r_closed
out = open("mstar.txt", "w")
for target in [0.5, 0.6, 0.7, 0.8, 0.86, 0.9, 0.95]:
    t = optimize.brentq(lambda t: rho_s(t) - target, 0.1, 80)
    gaps = {}
    for m in range(8, 61):
        c, a, b = best(m, t, tries=4)
        gaps[m] = c - target
        if c > target: break
    ms = [m for m in gaps if gaps[m] > 0]
    line = f"rho_S={target} theta={t:.4f} mstar={ms[0] if ms else '>60'} gap_at_mstar={gaps[ms[0]] if ms else max(gaps.values()):+.2e}"
    print(line, flush=True); out.write(line + "\n")
# figure 1 data: r(u) - affine fit at theta = 10 (and 3)
for t in [3, 10]:
    rs = rho_s(t); u = np.linspace(0.005, 0.995, 199)
    np.savetxt(f"fig_reg_t{t}.dat", np.c_[u, r_closed(u, t) - (0.5 + rs*(u - 0.5))], header="u gap", comments="")
# figure 2 data: best implied corr - rho_S vs m at theta = 10
t = 10; rs = rho_s(t)
rows = [(m, best(m, t, tries=4)[0] - rs) for m in range(2, 41)]
np.savetxt("fig_gap_t10.dat", np.array(rows), header="m gap", comments="")
