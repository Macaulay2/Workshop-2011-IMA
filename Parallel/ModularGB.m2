newPackage(
        "ModularGB",
        Version => "0.1", 
        Date => "",
        Authors => {{Name => "Mike Stillman", 
                  Email => "", 
                  HomePage => ""}},
        Headline => "modular groebner basis computations",
        DebuggingMode => true
        )

-- todo list:
-- 1. in the engine: improve all error checks.
-- 2. impelement over ZZ
-- 3. add documentation for the functions
-- 4. add tests
-- 5. collect benchmark examples
-- 6. work on certified result
-- 7. write documentation about how to program in the engine!!!
--




export {
     rationalConversion, chineseRemainder,myReduce, reconstruct, modGb}

debug Core
-- Code here

myReduce=method()
-- f should be an element of RQ
-- will return null if any of the denominators of the coefficients of f is not coprime to m
myReduce(RingElement,ZZ,Ring):=(f,m,RZ)->(
     tf:=terms f;
     sum(tf,t->(
	       e:=first exponents t; 
	       c:=leadCoefficient t;
	       (g,u,v):=toSequence gcdCoefficients(denominator c,m);
	       if g!=1 then return null;
	       d:=((numerator c)*u)%m;
	       d*RZ_e))
     )

rationalConversion=method()
rationalConversion(RingElement,ZZ,Ring):=(f,m,RQ)->new RQ from rawRingElementRatConversion(raw f,m, raw RQ)
rationalConversion(Matrix,ZZ,Ring):=(M,m,RQ)->(
     F:=RQ^(-degrees target M);
     G:=RQ^(-degrees source M);
     map(F,G,rawMatrixRatConversion(raw M,m,raw RQ))) 

chineseRemainder=method()
-- two polynomials over the integers, m and n coprime
chineseRemainder(RingElement,RingElement,ZZ,ZZ):=(f,g,m,n)->new (ring f) from rawRingElementCRA(raw f, raw g, m, n)
chineseRemainder(Matrix, Matrix, ZZ,ZZ):=(M,N,m,n)->map(ring M,rawMatrixCRA(raw M, raw N, m,n))

reconstruct=(f,primes,RQ)->(
      mZZ:=(f(primes_0),primes_0);
      print("lift:");
      time mQQ:=rationalConversion splice(mZZ,RQ);
      for i from 1 to #primes-1 do (
	   mZZ':=(f(primes_i),primes_i);
	   print("combine:");
	   time mZZ=(chineseRemainder(mZZ#0,mZZ'#0,mZZ#1,mZZ'#1),mZZ#1 * mZZ'#1);
	   oldmQQ:=mQQ;
	   print("lift:");
	   time mQQ=rationalConversion splice(mZZ,RQ);
	   if mQQ== oldmQQ then (
		<<"match at "<< i << endl;
		return mQQ);
	   );
      <<"d'oh! could not lift. Use more primes" << endl;
      )

modGb=(I,primes)->(
     RZ:=ZZ[gens ring I];
     query:=(p)->(
     	  Sp:=ZZ/p[gens ring I];
     	  phi:=map(Sp,ring I, vars Sp);
     	  Ip:=phi(I);
	  print("p="|toString(p));
          time sub(gens gb Ip,RZ));
     reconstruct(query,primes,ring I))       
     


     
     

TEST ///
R=QQ[x_0..x_5];
F = random(2,R);
RZ = ZZ(monoid R);
R32003 = (ZZ/32003)(monoid R)
f=sub(sub((map(R32003, R)) F, R32003),RZ);
Flifted=rationalConversion(f,32003,R);
assert(Flifted==F)
///

TEST ///
R=QQ[x_0..x_5];
F = random(R^2,R^{3:-1});
RZ = ZZ(monoid R);
R32003 = (ZZ/32003)(monoid R)
f=sub(sub((map(R32003, R)) F, R32003),RZ);
Flifted=rationalConversion(f,32003,R);
assert(Flifted==F)
///





end
parisilias13=(kk)->(    
     R=kk[S1,s1,d1,S2,D2,s2,d2];
     ideal(
	  -8*d1*D2+2*S2*s2-2*D2*d2-8*S2-4*s2+16,
           8*d1*D2-2*S2*s2+2*D2*d2+8*S2+4*s2-16
          -8*d1*S2-16*s1*D2+2*D2*s2-2*S2*d2+16*d1+8*D2+4*d2,
          8*d1*S2+16*s1*D2-2*D2*s2+2*S2*d2-16*d1-8*D2-4*d2,
          -8*S1*S2+4*S2^2-20*D2^2+16*S1-16,
          8*S1*S2-4*S2^2+20*D2^2-16*S1+16,
          -16*d1^2-8*s1*s2+s2^2-8*d1*d2-d2^2+32*s1-16,
          16*d1^2+8*s1*s2-s2^2+8*d1*d2+d2^2-32*s1+16,
          -16*S1*d1+8*d1*S2-10*D2*s2-4*S1*d2+2*S2*d2+16*d1+40*D2+4*d2,
          16*S1*d1-8*d1*S2+10*D2*s2+4*S1*d2-2*S2*d2-16*d1-40*D2-4*d2,
          -32*S1*s1+16*s1*S2+40*d1*D2+4*S1*s2-2*S2*s2+10*D2*d2+16*S1+32*s1-8*S2-4*s2-16,
          32*S1*s1-16*s1*S2-40*d1*D2-4*S1*s2+2*S2*s2-10*D2*d2-16*S1-32*s1+8*S2+4*s2+16,
          S2^2*s2^3-2*S2*D2*s2^3+D2^2*s2^3+3*S2^2*s2^2*d2-6*S2*D2*s2^2*d2+3*D2^2*s2^2*d2+3*S2^2*s2*d2^2-6*S2*D2*s2*d2^2+3*D2^2*s2*d2^2+S2^2*d2^3-2*S2*D2*d2^3+D2^2*d2^3-32,
          S2^2*s2^3+2*S2*D2*s2^3+D2^2*s2^3-3*S2^2*s2^2*d2-6*S2*D2*s2^2*d2-3*D2^2*s2^2*d2+3*S2^2*s2*d2^2+6*S2*D2*s2*d2^2+3*D2^2*s2*d2^2-S2^2*d2^3-2*S2*D2*d2^3-D2^2*d2^3-32,
          S1^2*s1^3-3*S1^2*s1^2*d1+3*S1^2*s1*d1^2-S1^2*d1^3+4*S1*s1^3*D2-12*S1*s1^2*d1*D2+12*S1*s1*d1^2*D2-4*S1*d1^3*D2+4*s1^3*D2^2-12*s1^2*d1*D2^2+12*s1*d1^2*D2^2-4*d1^3*D2^2-32,
          S1^2*s1^3+3*S1^2*s1^2*d1+3*S1^2*s1*d1^2+S1^2*d1^3-4*S1*s1^3*D2-12*S1*s1^2*d1*D2-12*S1*s1*d1^2*D2-4*S1*d1^3*D2+4*s1^3*D2^2+12*s1^2*d1*D2^2+12*s1*d1^2*D2^2+4*d1^3*D2^2-32))
 

beginDocumentation()

doc ///
Key
  ModularGB
Headline
Description
  Text
  Example
Caveat
SeeAlso
///

doc ///
Key
Headline
Usage
Inputs
Outputs
Consequences
Description
  Text
  Example
  Code
  Pre
Caveat
SeeAlso
///

TEST ///
-- test code and assertions here
-- may have as many TEST sections as needed
///


restart;
installPackage"ModularGB";
-- loadPackage"ModularGB";
--check"ModularGB";
kk=ZZ/101;
I=parisilias13(kk);
see=method()
see Ideal := (I)->netList I_*
time GB = gens gb I;

setRandomSeed("modGB");
#(primes=reverse(select(toList(30000..32000),i->isPrime i)))
sqrt(product (primes_{0..76}))
R=QQ[x_0..x_4];
I=ideal random(R^1,R^{10:-3});
time GB=gens gb I;
GB
leadTerm gens gb I
Imod= ideal modGb(I,primes);

makeMonic=(M)->(
     L:=flatten entries M;
     matrix{apply(L,f->(1/leadCoefficient(f) * f ))})

I1=makeMonic(gens gb I);
gens Imod - I1


leadTerm gens Imod  
netList  flatten entries gens Imod

describe ring M
RQ=QQ[x_0..x_4];
f=103/43714*x_0;
RZ=ZZ[x_0..x_4];
gcd(43714,23482340982311)
fred=myReduce(f,23482340982311,RZ)
rationalConversion(fred,23482340982311,RQ)

RZ=ZZ[x_0..x_4];
RQ=QQ[x_0..x_4];
f=103/43713*x_0;
factor 43713
m=3492034927;
n=33504331;
gcd(n,43713)
fm=myReduce(f,m,RZ)
fn=myReduce(f,n,RZ)
fmn=chineseRemainder(fm,fn,m,n);
rationalConversion(fmn,m*n,RQ)
