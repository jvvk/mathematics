"""Independent recheck of the triangle values of Corollary 2, sharing no code with triangle_exact.py or
triangle_closed.py. It uses the closed form g(a, b) = (Phi(a + b) - Phi(a - b)) / (2ab), with Phi even,
Phi(x) = x^2/2 - x^4/12 for |x| <= 1 and 2|x|/3 - 1/4 for |x| >= 1 (proved in Lean as g_closed), and
p = (1 / (2 sum L^2)) sum_k L_k^2 g(L_i^2/L_k^2, L_j^2/L_k^2) with side lengths from the law of sines."""
import math

def Phi(x):
    x = abs(x)
    return x * x / 2 - x ** 4 / 12 if x <= 1 else 2 * x / 3 - 0.25

def g(a, b):
    return (Phi(a + b) - Phi(a - b)) / (2 * a * b)

def p(A, B, C):
    S = [math.sin(math.radians(t)) ** 2 for t in (A, B, C)]
    return sum(S[k] * g(S[(k + 1) % 3] / S[k], S[(k + 2) % 3] / S[k]) for k in range(3)) / (2 * sum(S))

cases = [("equilateral", (60, 60, 60), 13 / 48), ("right isosceles", (90, 45, 45), 7 / 24),
         ("30-60-90", (90, 60, 30), 29 / 96), ("20-40-120", (20, 40, 120), None),
         ("flat isosceles (limit 25/72)", (1e-3, 1e-3, 180 - 2e-3), 25 / 72),
         ("needle isosceles (limit 1/3)", (90 - 1e-3, 90 - 1e-3, 2e-3), 1 / 3)]
for name, ang, exact in cases:
    v = p(*ang)
    print(f"{name:30s} p = {v:.6f}" + (f"   exact {exact:.6f}" if exact else ""))
