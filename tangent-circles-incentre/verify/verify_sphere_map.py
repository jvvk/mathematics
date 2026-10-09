"""Independent finite-difference checks of the eight-sheet sphere map.

No sampling estimate of the old 1/2 result. This checks a stronger new claim:
the total angular Jacobian of the inverse branches is pi at each sphere point.
Run single-core with timeout 120 nice -n 15.
"""
import math

pi = math.pi


def inverse(lon, height, a, b, sheet, linear_height=False):
    s = lon / 2
    z = 2*a*b*math.sin(s) / (
        (a+b)*math.cos(s)
        + math.sqrt((a+b)**2*math.cos(s)**2 + 4*a*b*math.sin(s)**2))
    p, q = math.atan(z/a), math.atan(z/b)
    v = pi*(height+1)/4
    eta = (pi/2-abs(s))*(height+1)/2 if linear_height else math.asin(math.cos(s)*math.sin(v))
    sign, pa, qb = sheet
    omega = p-q + sign*eta
    ex, ey = math.cos(omega), math.sin(omega)
    ma, mb = a*ex+z*ey, b*ex-z*ey
    ca, cb = math.sqrt(ma*ma-z*z), math.sqrt(mb*mb-z*z)
    sp, sq = -ma+pa*ca, mb+qb*cb
    px, py = sp*ex, z+sp*ey
    qx, qy = sq*ex, z+sq*ey
    return math.atan2(py, px+a), math.atan2(qy, qx-b)


SHEETS = [(s, p, q) for s in (-1, 1) for p in (-1, 1) for q in (-1, 1)]


def angle_difference(x, y):
    return math.atan2(math.sin(x-y), math.cos(x-y))


def density_error(a, b, lon, height, sheets=SHEETS, linear_height=False):
    eps = 2e-6
    total = 0.
    for sheet in sheets:
        lu = inverse(lon+eps, height, a, b, sheet, linear_height)
        ld = inverse(lon-eps, height, a, b, sheet, linear_height)
        hu = inverse(lon, height+eps, a, b, sheet, linear_height)
        hd = inverse(lon, height-eps, a, b, sheet, linear_height)
        dl = [angle_difference(x, y)/(2*eps) for x, y in zip(lu, ld)]
        dh = [angle_difference(x, y)/(2*eps) for x, y in zip(hu, hd)]
        total += abs(dl[0]*dh[1]-dl[1]*dh[0])
    return abs(total/pi-1)


def sphere_map(px, py, qx, qy, a, b, plain_average=False):
    z = (py+qy)/2 if plain_average else (qx*py-px*qy)/(qx-px)
    p, q = math.atan(z/a), math.atan(z/b)
    s, d = p+q, p-q
    omega = math.atan2(qy-py, qx-px)
    eta = omega-d
    v = abs(math.asin(max(-1., min(1., math.sin(eta)/math.cos(s)))))
    return 2*s, 4*v/pi-1


cases = [(a,b,l,h) for a,b in ((1,1),(1,2),(.1,5),(7,.3))
         for l in (-2.4,-.8,.4,2.5) for h in (-.7,-.2,.35,.8)]
errors = [density_error(*c) for c in cases]
assert max(errors) < 2e-5, max(errors)
print(f'PASS inverse area: {len(cases)} points, 8 sheets each; max relative error {max(errors):.3g}')
for name, kw in [('drop one sheet', {'sheets':SHEETS[:-1]}),
                 ('linear height in eta', {'linear_height':True})]:
    bad = sum(density_error(*c, **kw) > 2e-5 for c in cases)
    assert bad > 0, name
    print(f'REJECT mutant {name}: {bad}/{len(cases)} area checks fail')

roundtrip = []
plain_errors = 0
for c in cases:
    a,b,lon,height = c
    for sheet in SHEETS:
        theta,phi = inverse(lon,height,a,b,sheet)
        coords = (-a+a*math.cos(theta),a*math.sin(theta),
                  b+b*math.cos(phi),b*math.sin(phi))
        ll,hh = sphere_map(*coords,a,b)
        roundtrip.append(max(abs(ll-lon),abs(hh-height)))
        ml,mh = sphere_map(*coords,a,b,plain_average=True)
        plain_errors += max(abs(ml-lon),abs(mh-height)) > 1e-7
assert max(roundtrip) < 1e-7, max(roundtrip)
assert plain_errors > 0
print(f'PASS round trips: {len(roundtrip)}, max error {max(roundtrip):.3g}')
print(f'REJECT mutant plain y-average crossing: {plain_errors}/{len(roundtrip)} round trips fail')


def cross(u,v):
    return u[0]*v[1]-u[1]*v[0]


def sub(u,v):
    return (u[0]-v[0],u[1]-v[1])


def contains(pts, point):
    # Generic barycentric determinant test: independent of sectors and spheres.
    p,q,r = pts
    area = cross(sub(q,p),sub(r,p))
    nums = [cross(sub(q,point),sub(r,point)),
            cross(sub(r,point),sub(p,point)),
            cross(sub(p,point),sub(q,point))]
    return all(x*area > 0 for x in nums)


checked = wrong_lunes = 0
for a,b,c in ((1,1,1),(1,2,3),(.1,1,5),(2,7,.3)):
    total = a+b+c
    rho = math.sqrt(a*b*c/total)
    cx = -a+((a+c)**2+(a+b)**2-(b+c)**2)/(2*(a+b))
    cy = math.sqrt((a+c)**2-(cx+a)**2)
    centres, radii, inc = [(-a,0),(b,0),(cx,cy)], [a,b,c], (0,rho)
    for n in range(1,1001):
        angles = [2*pi*((n*k+.137)%1) for k in (math.sqrt(2),math.sqrt(3),math.sqrt(5))]
        pts = [(o[0]+rr*math.cos(t),o[1]+rr*math.sin(t))
               for o,rr,t in zip(centres,radii,angles)]
        misses, mutant = [], []
        for j,k,opp in ((0,1,2),(1,2,0),(2,0,1)):
            aa,bb = radii[j],radii[k]
            e = tuple(x/(aa+bb) for x in sub(centres[k],centres[j]))
            touch = (centres[j][0]+aa*e[0],centres[j][1]+aa*e[1])
            normal = tuple(x/rho for x in sub(inc,touch))
            def local(pt):
                x = sub(pt,touch)
                return x[0]*e[0]+x[1]*e[1], x[0]*normal[0]+x[1]*normal[1]
            pp,qq = local(pts[j]),local(pts[k])
            lon,height = sphere_map(*pp,*qq,aa,bb)
            u,v = sub(centres[j],centres[opp]),sub(centres[k],centres[opp])
            angle = math.acos(sum(x*y for x,y in zip(u,v))/(math.hypot(*u)*math.hypot(*v)))
            misses.append(lon > pi-angle)
            mutant.append(lon > angle)  # Deliberately use the wrong meridian.
        truth = contains(pts,inc)
        assert sum(misses) <= 1
        assert truth == (not any(misses)), (a,b,c,n)
        wrong_lunes += truth != (not any(mutant))
        checked += 1
assert wrong_lunes > 0
print(f'PASS triangle/lune equivalence and disjointness: {checked} deterministic triangles')
print(f'REJECT mutant meridian C instead of pi-C: {wrong_lunes}/{checked} triangles fail')
