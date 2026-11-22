\\ Independent count of the singular points of the foliation q = gradF x gradG on the dual plane.
F = y^3 - x^2*y; G = z^3 - x^2*z;
gF = [deriv(F,x), deriv(F,y), deriv(F,z)]; gG = [deriv(G,x), deriv(G,y), deriv(G,z)];
cr(a,b) = [a[2]*b[3]-a[3]*b[2], a[3]*b[1]-a[1]*b[3], a[1]*b[2]-a[2]*b[1]];
q = cr(gF, gG); E = cr([x,y,z], q);
\\ chart x = 1: points (1, y, z). Eliminate z, factor, then test each root.
E1 = subst(E, x, 1);
R = gcd(polresultant(E1[1], E1[2], z), polresultant(E1[1], E1[3], z));
R = gcd(R, polresultant(E1[2], E1[3], z));
print("eliminant in y (chart x=1): ", factor(R));
cnt = 0;
{
  fa = factor(R)[,1];
  for (i = 1, #fa,
    my(K = nfinit(fa[i]), pol);
    \\ common z-solutions over the field y = root of fa[i]
    pol = gcd(gcd(Mod(E1[1], fa[i]), Mod(E1[2], fa[i])), Mod(E1[3], fa[i]));
    pol = lift(pol);
    print("  y-factor ", fa[i], " -> z-polynomial ", pol);
    cnt += poldegree(fa[i]) * poldegree(pol, z);
  );
}
\\ chart x = 0, y = 1
E2 = subst(subst(E, x, 0), y, 1);
g2 = gcd(gcd(E2[1], E2[2]), E2[3]);
print("chart x=0,y=1 common z-poly: ", g2);
cnt += poldegree(g2, z);
E3 = subst(subst(subst(E, x, 0), y, 0), z, 1);
print("point (0,0,1) singular: ", E3 == [0,0,0]);
cnt += (E3 == [0,0,0]);
print("total singular points: ", cnt);
\\ Redo the 3y^2-1 factor over K = Q(t), t^2 = 3, y = t/3 * s (s = +-1), as polynomials in z over K.
{
  my(tot = 0);
  foreach([1, -1], sg,
    my(yy = Mod(sg*t/3, t^2 - 3), P1, P2, P3, g);
    P1 = subst(E1[1], y, yy); P2 = subst(E1[2], y, yy); P3 = subst(E1[3], y, yy);
    g = gcd(gcd(P1, P2), P3);
    print("  y = ", sg, "/sqrt3 -> z-gcd ", g);
    tot += poldegree(g, z));
  print("sqrt3 points: ", tot, "   corrected total: ", 9 + tot + 1 + 1);
}
