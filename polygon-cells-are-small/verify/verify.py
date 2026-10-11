"""Finite ingredient audit, not a proof of the all-n area theorem. Stdlib only."""
import math
import argparse

TAU = 2 * math.pi
COUNT = 0
MUTANT = ""

def check(ok, message):
    global COUNT
    COUNT += 1
    assert ok, message

def bisect(fn, lo, hi):
    flo = fn(lo)
    for _ in range(65):
        mid = (lo + hi) / 2
        if fn(mid) * flo > 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2

def curve(rho, phi):
    return math.acos(rho * math.cos(phi))

def gp(rho, phi):
    return rho * math.sin(phi) / math.sqrt(1 - rho*rho*math.cos(phi)**2)

def gpp(rho, phi):
    factor = 1 if MUTANT == "drop_curvature_factor" else 1-rho*rho
    return rho * factor * math.cos(phi) / (1-rho*rho*math.cos(phi)**2)**1.5

def enclosure(lines):
    """Independent intersection of the actual four halfplanes relative to x."""
    verts = []
    for i, (a, b, c) in enumerate(lines):
        for d, e, f in lines[i+1:]:
            det = a*e-b*d
            if abs(det) < 1e-12:
                continue
            x, y = (c*e-b*f)/det, (a*f-c*d)/det
            if all(p*x+q*y <= z+1e-7 for p,q,z in lines):
                verts.append((x,y))
    angles = sorted(math.atan2(b,a) % TAU for a,b,c in lines)
    gaps = [(angles[(i+1)%len(angles)]-angles[i]) % TAU for i in range(len(angles))]
    check(max(gaps) < math.pi-0.1, "halfplanes do not bound a cell")
    check(len(verts) >= 3, "missing enclosing polygon")
    return max(math.hypot(x,y) for x,y in verts)

def rational_trap(n, rho, beta):
    t = math.pi/n
    R = 1/(2*math.sin(t))
    if MUTANT == "wrong_scale":
        R = 1
    check(abs(2*R*math.sin(t)-1) < 1e-12, "side-length scaling")
    left, right = 5*math.pi/24, 7*math.pi/24
    delta = gp(rho,right)-gp(rho,left)
    b = 2
    while b*delta < 8:
        b *= 2
    a = int(b*(gp(rho,left)+gp(rho,right))/2)
    if a % 2 == 0:
        a += 1
    check(math.gcd(a,b)==1 and a%2==1, "primitive odd numerator")
    check(gp(rho,left) < a/b < gp(rho,right), "rational tangent in interval")
    phi0 = bisect(lambda z: gp(rho,z)-a/b,left,right)
    w = max(4*b*t, math.sqrt(t))
    Jlo, Jhi = math.pi/12, 5*math.pi/12
    check(phi0-w > Jlo and phi0+w < Jhi, "outside admissible regime")
    lines=[]
    for orientation in (1,-1):
        aa = orientation*a
        center = orientation*phi0
        f = lambda z: b*curve(rho,z)-aa*z
        target=max(f(center-w),f(center+w))+2*t
        phase = aa*beta
        k=math.ceil((target-phase)/t)
        level=phase+k*t
        lo,hi = (Jlo,Jhi) if orientation==1 else (-Jhi,-Jlo)
        check(f(lo)>level and f(hi)>level, "level too high for bracket")
        root = bisect(lambda z:f(z)-level,lo,center)
        # b*v-aa*u=k, u==v (mod 2), hence (b-aa)j-(b+aa)i=k.
        # The primitive lattice has u-step 2b.
        u0=(k*pow(b-aa,-1,2*b))%(2*b)
        phi_phase=0 if MUTANT=="omit_phase" else beta
        step=math.floor(((root+phi_phase)/t-u0)/(2*b))
        signs=[]
        pair=[]
        for jstep in (step,step+1):
            if MUTANT=="one_sided":
                jstep=step
            u=u0+2*b*jstep
            v=(k+aa*u)//b
            if MUTANT=="wrong_parity":
                v+=1
            phi=u*t-phi_phase
            d=v*t
            check(u%2==v%2, "invalid endpoint parity")
            ii,jj=((u-v)//2)%n,((u+v)//2)%n
            check((jj-ii)%n not in (0,1,n-1), "not a diagonal")
            actual_phi=phi+beta
            for idx in (ii,jj):
                # Direct endpoint equation, independent of curve and residue calculation.
                value=math.cos(2*idx*t-actual_phi)-math.cos(d)
                check(abs(value)<5e-8, "line does not join the claimed vertices")
            gg=curve(rho,phi)
            residual=2*R*math.sin((gg+d)/2)*math.sin((d-gg)/2)
            signs.append(residual)
            pair.append((phi,d))
            check(abs(phi-center) < 10*(math.sqrt(t)+b*t), "normal drift")
            check(abs(residual) < 1000*(math.sqrt(t)+b*t), "distance estimate")
            sign=1 if residual>0 else -1
            lines.append((-sign*math.cos(phi),-sign*math.sin(phi),abs(residual)))
        check(signs[0]*signs[1]<0, "chords fail to straddle point")
        check(pair[0][0] < root < pair[1][0], "lattice root bracket")
    rad=enclosure(lines)
    check(rad < 2000*(math.sqrt(t)+b*t), "actual enclosure violates scale")
    return rad/(math.sqrt(t)+b*t)

def basic_audit():
    for rho in (.02,.1,.3,.5,.8,.95,.99):
        kappa=rho*(1-rho*rho)
        for j in range(31):
            phi=math.pi/12+j*math.pi/90
            eps=1e-5
            independent=(gp(rho,phi+eps)-gp(rho,phi-eps))/(2*eps)
            check(abs(independent-gpp(rho,phi)) < 1e-6, "wrong curvature")
            check(.25*kappa < gpp(rho,phi) < 64*kappa, "uniform curvature bounds")
    for n in range(4,105):
        t=math.pi/n
        R=1/(2*math.sin(t))
        for parity in (0,1):
            levels=sorted({-R,R,*[R*math.cos(v*t) for v in range(parity,n+1,2)]})
            check(max(y-x for x,y in zip(levels,levels[1:])) <= 2*R*t+1e-12,"parallel-strip gap")
    # Exact geometric obstruction to including the odd central cell in rotational packing.
    n=101
    t=math.pi/n
    R=1/(2*math.sin(t))
    apothem=R*math.sin(t/2)
    center_area=n*apothem**2*math.tan(t)
    check(center_area > math.pi/16,"central cell remains macroscopic")
    if MUTANT=="include_central":
        check(apothem < 0,"central cell rotational images should be disjoint")
    # A boundary cell retains an edge of length 1, so a global diameter theorem is false.
    if MUTANT=="global_diameter":
        check(1 <= 100/math.sqrt(1_000_000),"boundary diameter contradicts global shrinkage")

def inner_trap(n,r,beta):
    t=math.pi/n
    R=1/(2*math.sin(t))
    v=round(math.acos(r/(2*R))/t)
    a=R*math.cos(v*t)
    check(abs(a-r/2)<1,"inner offset rounding")
    phi0=math.acos(a/r)
    lines=[]
    for root in (-phi0,phi0):
        j=math.floor(((root+beta)/t-v)/2)
        signs=[]
        for jj in (j,j+1):
            u=v+2*jj
            phi=u*t-beta
            residual=r*math.cos(phi)-a
            signs.append(residual)
            check(abs(residual)<=2*r*t+1e-9,"inner chord distance")
            sign=1 if residual>0 else -1
            lines.append((-sign*math.cos(phi),-sign*math.sin(phi),abs(residual)))
        check(signs[0]*signs[1]<0,"inner pair does not straddle")
    rad=enclosure(lines)
    check(rad<10*r*t,"inner enclosure")

def main():
    global MUTANT
    parser=argparse.ArgumentParser()
    parser.add_argument("--mutant",default="")
    MUTANT=parser.parse_args().mutant
    basic_audit()
    for n in (100_003,1_000_003):
        for r in (10,30,.5*math.sqrt(n),math.sqrt(n)):
            for beta in (.123,.456,1.234,2.345):
                inner_trap(n,r,beta)
    ratios=[]
    for n in (1_000_003,10_000_019,100_000_007):
        for rho in (.01,.02,.05,.1,.25,.5,.75,.9,.95,.98,.99):
            for beta in (.123,.456,1.234,2.345):
                ratios.append(rational_trap(n,rho,beta))
    print(f"PASS: {COUNT} assertions; 132 rational and 32 inner point traps; max rational enclosure/scale {max(ratios):.6f}")

if __name__=="__main__":
    main()
