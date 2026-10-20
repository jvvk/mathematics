"""Deterministic disk stacking with an affine diameter law on circumference one.

Candidate tangencies are solved by subtracting their two quadratic equations.
Overlap checks include every previously placed disk whose vertical interval can
intersect the candidate. No finite history window or front-only cutoff is used.
"""
from __future__ import annotations

from bisect import bisect_left, bisect_right, insort
from dataclasses import dataclass
import math


@dataclass(frozen=True)
class Disk:
    x: float
    y: float
    d: float


def seed(beta: float, eps: float, c: float, consistent: bool = True):
    """Return a three-disk front, intercept b0, and its three bearings.

    For consistent seeds the edge lengths are solved exactly from tangency and
    the affine law. Vertical closure gives the explicit down-angle formula.
    Equal-diameter seeds reproduce the original exploratory convention.
    """
    a, b = beta + eps / 2, beta - eps / 2
    sa, sb = math.sin(a), math.sin(b)
    sd = -(sa + sb) / (1 + c*c*sa*sb/4) if consistent else -(sa + sb)
    if abs(sd) >= 1:
        raise ValueError('Seed does not have a right-pointing down edge')
    down = math.asin(sd)
    angles = (down, a, b)
    pts = [(0.0, 0.0, 1.0)]
    x = y = 0.0
    for angle in angles:
        local_d = 1 + c*y if consistent else 1.0
        length = local_d / (1 - c*math.sin(angle)/2) if consistent else 1.0
        x += length*math.cos(angle)
        y += length*math.sin(angle)
        pts.append((x, y, 1+c*y if consistent else 1.0))
    if abs(y) > 5e-13:
        raise ArithmeticError('Seed failed vertical closure')
    scale = 1/x
    return [Disk(px*scale, py*scale, pd*scale) for px,py,pd in pts[:-1]], scale, angles


def apex(P: Disk, R: Disk, b0: float, c: float):
    """Upper tangency branch; return None if no real positive-diameter branch.

    Local coordinates about P keep the quadratic well-conditioned after long runs.
    """
    dx, dy = R.x-P.x, R.y-P.y
    if dx <= 0:
        return None
    law_p = b0+c*P.y
    sp, sr = (P.d+law_p)/2, (R.d+law_p)/2
    k = (dy+c*(R.d-P.d)/4)/dx
    x0 = (dx*dx+dy*dy-sr*sr+sp*sp)/(2*dx)
    A = 1+k*k-c*c/4
    B = -2*x0*k-sp*c
    C = x0*x0-sp*sp
    discriminant = B*B-4*A*C
    if discriminant < 0 or A <= 0:
        return None
    root = math.sqrt(discriminant)
    q = -0.5*(B+math.copysign(root,B))
    roots = (-B/(2*A),) if q == 0 else (q/A,C/q)
    y = max(roots)
    x = x0-k*y
    diameter = law_p+c*y
    if diameter <= 0 or dx*y-dy*x <= 0:
        return None
    return Disk(P.x+x,P.y+y,diameter)


class Stack:
    def __init__(self, beta, eps, c, *, consistent=True, tol=1e-11):
        self.disks, self.b0, _ = seed(beta,eps,c,consistent)
        self.front = list(range(3))
        self.c = c
        self.tol = tol
        self.by_y = sorted((p.y,i) for i,p in enumerate(self.disks))
        self.max_d = max(p.d for p in self.disks)
        self.steps = 0

    def pair(self):
        ys = [self.disks[i].y for i in self.front]
        n = sum(ys[(i+1)%len(ys)] < y for i,y in enumerate(ys))
        return n,len(ys)-n

    def free(self,Q, parents):
        radius = (self.max_d+Q.d)/2
        lo = bisect_left(self.by_y,(Q.y-radius,-1))
        hi = bisect_right(self.by_y,(Q.y+radius,len(self.disks)))
        for _,i in self.by_y[lo:hi]:
            P = self.disks[i]
            # Tangency to the chosen images is imposed by the quadratic solve.
            # Do not reject it because global-coordinate subtraction rounds.
            # A closer periodic image of a parent must still be tested.
            if i in parents and abs(parents[i].x-Q.x) <= 0.5:
                continue
            dx = (P.x-Q.x+0.5)%1-0.5
            distance = math.hypot(dx,P.y-Q.y)
            threshold = (P.d+Q.d)/2
            if distance < threshold-self.tol:
                return False
        return True

    def step(self):
        F, N = self.front, len(self.front)
        best = None
        for a in range(N):
            for gap in range(N-1):
                j = (a+gap+1)%N
                P,R = self.disks[F[a]],self.disks[F[j]]
                if j <= a:
                    R=Disk(R.x+1,R.y,R.d)
                Q=apex(P,R,self.b0,self.c)
                if Q is None or (best is not None and Q.y >= best[0].y):
                    continue
                if self.free(Q,{F[a]:P,F[j]:R}):
                    best=Q,a,gap
        if best is None:
            raise ArithmeticError(f'No admissible disk at step {self.steps+1}')
        Q,a,gap=best
        remove={F[(a+t+1)%N] for t in range(gap)}
        new_id=len(self.disks)
        Q=Disk(Q.x%1,Q.y,Q.d)
        self.disks.append(Q)
        insort(self.by_y,(Q.y,new_id))
        self.max_d=max(self.max_d,Q.d)
        self.front=sorted([i for i in F if i not in remove]+[new_id],key=lambda i:self.disks[i].x)
        self.steps+=1
        return ('T' if gap==0 else 'R' if gap==1 else 'P' if gap==2 else f'G{gap}'),gap


def run(beta,eps,c,*,consistent=True,tol=1e-11,target=(3,5),max_steps=None,record=False):
    S=Stack(beta,eps,c,consistent=consistent,tol=tol)
    base=(1,2)
    cur=base
    events=[]
    max_steps=max_steps or math.ceil(20/abs(c))
    reason='step_limit'
    for _ in range(max_steps):
        kind,gap=S.step()
        pair=S.pair()
        if kind!='R' or pair!=cur:
            events.append(dict(step=S.steps,kind=kind,before=list(cur),after=list(pair)))
        if gap>=2:
            reason='pentagon' if gap==2 else 'higher_transition'
            break
        if pair!=cur:
            smaller=0 if base[0]<base[1] else 1
            expected=list(cur)
            expected[smaller]+=1
            if pair!=tuple(expected) or kind!='T':
                reason='wrong_side'
                break
            cur=pair
            if cur[smaller]==sum(base):
                base=cur
                if base==target:
                    reason='target'
                    break
    result=dict(beta=beta,eps=eps,c=c,ratio=eps/abs(c),seed='consistent' if consistent else 'equal',
                tolerance=tol,steps=S.steps,outcome=reason,events=events)
    return (result,S) if record else result
