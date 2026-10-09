"""Exact local checks for the diameter theorem and its sharpness family.

These check specific algebraic statements, not the complete topological proof.
Run with the same Python environment as verify.py (SymPy and z3-solver).
"""
import json
from pathlib import Path
import sympy as sp
import z3

results = {}


def exclude(name, constraints):
    solver = z3.SolverFor('QF_NRA')
    solver.set(timeout=30000)
    solver.add(*constraints)
    answer = solver.check()
    record = {'result': str(answer)}
    if answer == z3.unknown:
        record['reason'] = solver.reason_unknown()
    elif answer == z3.sat:
        record['countermodel'] = str(solver.model())
    results[name] = record
    assert answer == z3.unsat, (name, record)


# Median points other than the apex have no unit neighbour in the triangle:
# it suffices to bound their squared distances to the three corners.
a, h, y = z3.Reals('a h y')
exclude('median_corner_distance_negation', [
    a > 0, a < 1, h > 0, a*a+h*h == 1, y >= 0, y < h,
    z3.Or(a*a+y*y >= 1, (h-y)*(h-y) >= 1),
])

# In one closed half, the unique unit pair consists of the endpoints of
# its sloping side. Coefficients locate arbitrary points in that half.
l, t, m, u = z3.Reals('l t m u')
px, py, qx, qy = -a*l, h*t, -a*m, h*u
is_lz = z3.And(l == 1, t == 0, m == 0, u == 1)
is_zl = z3.And(l == 0, t == 1, m == 1, u == 0)
exclude('half_triangle_unit_pair_negation', [
    a > 0, a < 1, h > 0, a*a+h*h == 1,
    l >= 0, t >= 0, l+t <= 1, m >= 0, u >= 0, m+u <= 1,
    (px-qx)**2+(py-qy)**2 == 1, z3.Not(z3.Or(is_lz, is_zl)),
])

# At C, normalize the hull cone between CA and CE to the quadrant x<0,y>0.
# F=(-u,v), B=(-bx,by), D=(-dx,dy); the side conditions force a reflex C.
u, v, bx, by, dx, dy = z3.Reals('u v bx by dx dy')
exclude('final_ray_order_turn_negation', [
    u > 0, v > 0, bx > 0, by > 0, dx > 0, dy > 0,
    u*by > v*bx, u*dy < v*dx, bx*dy-by*dx >= 0,
])

# The mixed-turn pocket chord is obtained by summing its three edge vectors.
alpha, beta = sp.symbols('alpha beta', real=True)
endpoint = (
    1-sp.cos(alpha)+sp.cos(beta-alpha),
    sp.sin(alpha)+sp.sin(beta-alpha),
)
formula = 3-2*sp.cos(alpha)-2*sp.cos(beta)+2*sp.cos(alpha-beta)
assert sp.trigsimp(sp.expand_trig(sum(q*q for q in endpoint)-formula)) == 0
results['opposite_turn_chord_formula'] = {'result': 'exact identity verified'}

# The strengthened proof excludes four consecutive unit hull edges.
gamma = sp.symbols('gamma', real=True)
directions = [0, sp.pi-alpha, 2*sp.pi-alpha-beta,
              3*sp.pi-alpha-beta-gamma]
edges = [sp.Matrix([sp.cos(q), sp.sin(q)]) for q in directions]
last = sum(edges, sp.zeros(2, 1))
incoming, outgoing = edges[-1], -last
cross = incoming[0]*outgoing[1]-incoming[1]*outgoing[0]
formula = sp.sin(gamma)-sp.sin(beta+gamma)+sp.sin(alpha+beta+gamma)
assert sp.trigsimp(sp.expand_trig(cross-formula)) == 0
bound = sp.sin(gamma)-sp.sin(beta+gamma)+sp.sin(2*gamma+beta)
factor = 4*sp.sin(gamma/2)*sp.cos((beta+gamma)/2)*sp.cos(gamma+beta/2)
assert sp.trigsimp(sp.expand_trig(bound-factor)) == 0
assert last.subs({alpha: sp.pi/2, beta: sp.pi/2, gamma: sp.pi/2}) == sp.zeros(2, 1)
results['four_hull_edges_turn_formula'] = {'result': 'exact identity verified'}
results['four_hull_edges_endpoint_factorization'] = {'result': 'exact identity verified'}

# Exact sharpness-family identities, including the sign-controlling factor.
t = sp.symbols('t', positive=True)
d = sp.Matrix([2*t*t/(1+t*t), 1+2*t/(1+t*t)])
e = d+sp.Matrix([sp.Rational(3, 5), -sp.Rational(4, 5)])
assert sp.factor(sum((d[k]-[1,1][k])**2 for k in [0,1])-1) == 0
assert sp.factor(2*e[1]-e.dot(e)-16*t*(1-2*t)/(5*(1+t*t))) == 0
r2 = e.dot(e)
f = e/2+sp.sqrt(1/r2-sp.Rational(1,4))*sp.Matrix([-e[1], e[0]])
assert sp.simplify(f.dot(f)-1) == 0
assert sp.simplify((f-e).dot(f-e)-1) == 0
assert sp.simplify(f.subs(t, 0)) == sp.Matrix([0,1])
results['sharpness_family_identities'] = {'result': 'exact identities verified'}

# Fixed rational parameters give exact algebraic controls for simplicity.
# Import the existing geometry audit while suppressing its control report.
import contextlib
import io
with contextlib.redirect_stdout(io.StringIO()):
    from verify import audit, sign, orient
controls = []
for value in [sp.Rational(1,1000), sp.Rational(1,100), sp.Rational(1,20),
              sp.Rational(1,4), sp.Rational(49,100)]:
    dd, ee, ff = [tuple(sp.simplify(q.subs(t,value)) for q in v) for v in [d,e,f]]
    points = [(0,0),(1,0),(1,1),dd,ee,ff]
    record = audit(points)
    assert record['unit'] and record['distinct'] and record['simple']
    assert not record['contained']
    turns = [sign(orient(points[i-1], points[i], points[(i+1)%6]))
             for i in range(6)]
    assert turns == [1, 1, 1, 1, -1, 1]
    assert sign(ff[0]) < 0 and sign(ff[1]) > 0 and sign(1-ff[1]) > 0
    assert all(sign(q)>0 and sign(1-q)>0 for q in ee)
    record['t'] = str(value)
    record['bounding_square_side'] = float(max(1-ff[0],dd[1]))
    record['turn_signs'] = turns
    controls.append(record)
results['sharpness_family_exact_controls'] = controls

target = Path(__file__).with_name('manuscript-checks.json')
target.write_text(json.dumps(results, indent=2)+'\n')
print(json.dumps(results, indent=2))
