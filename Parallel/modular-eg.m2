R = ZZ[a..d]
F = 3*a^2-5
G = 5*a^2+7
new R from rawRingElementCRA(raw F, raw G, 11, 13)

M = matrix{{F}}
N = matrix{{G}}
rawMatrixCRA(raw M, raw N, 11, 13)


TEST ///
restart
debug Core
 
R=QQ[x_0..x_5];
F = random(2,R);
F = 0_R
F = 0_R
RZ = ZZ (monoid R);
R32003 = (ZZ/32003)(monoid R)
R32009 = (ZZ/32009)(monoid R)

f1 = sub((map(R32003, R)) F, RZ);
f2 = sub((map(R32009, R)) F, RZ);

time g = new RZ from rawRingElementCRA(raw f1, raw f2, 32003, 32009);
///

g1 = sub(sub(g, R32003), RZ);
g2 = sub(sub(g, R32009), RZ);
f1 == g1
f2 == g2




TEST ///
restart
debug Core
 
R=QQ[x_0..x_5];
F = random(2,R);
RZ = ZZ (monoid R);
F = 0_RZ
G = (x_0^2+ 42); 
time g1 = new RZ from rawRingElementCRA(raw F, raw F, 32003, 32009);
time g2 = new RZ from rawRingElementCRA(raw F, raw G, 32003, 32009);
time g3 = new RZ from rawRingElementCRA(raw G, raw F, 32003, 32009);
g2 % 32003, g2 % 32009
g3 % 32009, g3 % 32003
(g1,g2,g3)
///



TEST ///
restart
debug Core
 
R=QQ[x_0..x_5];
F = random(R^2,R^{2:-1})
RZ = ZZ (monoid R);
primes=select(32000..32500,p-> isPrime p);
Rp=apply(primes,i->(ZZ/i)(monoid R));
fp=apply(#primes,i->sub( (map(Rp_i,R)) F, RZ))
m=map(RZ,rawMatrixCRA(raw fp#0, raw fp#1, primes#0,primes#1))

CRAcheck=(M,N,p,q)->(
     m:=map(RZ,rawMatrixCRA(raw M, raw N, p,q));
     ch1:=apply(flatten entries m, f-> f % sub(p,RZ)) == flatten entries M;
     ch2:=apply(flatten entries m, f-> f % sub(q,RZ)) == flatten entries N;
     ch1 and ch2)


q=primes#0;
m=fp_0;
scan(1..#primes-1,i->(
	  m=map(RZ,rawMatrixCRA(raw m, raw fp#i, q, primes#i));
	  q=q*primes#i));
 apply(#primes,i->sub(sub(m, Rp_i),RZ) == fp_i)

CRAcheck(fp#0,fp#1,primes#0,primes#1)

time g = new RZ from rawRingElementCRA(raw f1, raw f2, 32003, 32009);
///