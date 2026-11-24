"""Closed form of E[V|U=u] for Frank vs quadrature; pole at u = 2*pi*i/t."""
import numpy as np
from scipy import integrate
from intscores import C
def r_closed(u, t):
    x = np.exp(-t*u)-1; a = np.exp(-t)-1
    return 1 - np.exp(-t*u)*(x - a*u)/(x*(x - a))
def r_quad(u, t, h=1e-6):
    return 1 - integrate.quad(lambda v: (C(u+h, v, t)-C(u-h, v, t))/(2*h), 0, 1, epsabs=1e-12)[0]
if __name__ == "__main__":
    worst = 0
    for t in [0.3, 1, 3, 10, 40, -2, -7]:
        for u in np.linspace(0.01, 0.99, 25):
            worst = max(worst, abs(r_closed(u, t)-r_quad(u, t)))
    print("max |closed - quad| =", worst)
    t = 10; z0 = 2j*np.pi/t
    for eps in [1e-2, 1e-4, 1e-6]:
        print(eps, abs(r_closed(z0+eps, t))*eps)   # ~ constant residue if simple pole
