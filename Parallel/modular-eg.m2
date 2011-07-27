R = ZZ[a..d]
F = 3*a^2-5
G = 5*a^2+7
new R from rawRingElementCRA(raw F, raw G, 11, 13)

M = matrix{{F}}
N = matrix{{G}}
rawMatrixCRA(raw M, raw N, 11, 13)


restart
debug Core

R=QQ[x_0..x_5];
F = random(12,R);
F = 485738495743895734895738957389574398573489573489573498573498101_R
F = 0_R
RZ = ZZ (monoid R);
R32003 = (ZZ/32003)(monoid R)
R32009 = (ZZ/32009)(monoid R)

f1 = sub((map(R32003, R)) F, RZ);
f2 = sub((map(R32009, R)) F, RZ);
time g = new RZ from rawRingElementCRA(raw f1, raw f2, 32003, 32009);
g1 = sub(sub(g, R32003), RZ);
g2 = sub(sub(g, R32009), RZ);
f1 == g1
f2 == g2
