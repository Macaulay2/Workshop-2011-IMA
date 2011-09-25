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
-- 0. write tests for rational Conversion.
-- 1. in the engine: improve all error checks.
-- 2. impelement over ZZ
-- 3. add documentation for the functions
-- 4. add tests
-- 5. collect benchmark examples: get ALL examples from Pfister's paper into M2
-- 6. work on certified result
-- 7. write documentation about how to program in the engine!!!
--

export {
     rationalConversion, chineseRemainder,myReduce, reconstruct, modGb,reduceViaPrimes, majorityRule}

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
     print("----");
     F:=RQ^(-degrees target M);
     G:=RQ^(-degrees source M);
     map(F,G,rawMatrixRatConversion(raw M,m,raw RQ))) 

chineseRemainder=method()
-- two polynomials over the integers, m and n coprime
chineseRemainder(RingElement,RingElement,ZZ,ZZ):=(f,g,m,n)->new (ring f) from rawRingElementCRA(raw f, raw g, m, n)
chineseRemainder(Matrix, Matrix, ZZ,ZZ):=(M,N,m,n)->map(ring M,rawMatrixCRA(raw M, raw N, m,n))
chineseRemainder(List,List):=(Ms,ms)->(
     -- Ms is a list of matrices over RZ
     -- ms is a list of pairwise coprime integers
     Mr:=Ms_0;
     mr:=ms_0;
     for i from 1 to #Ms-1 do (
	  Mr=chineseRemainder(Mr,Ms_i,mr,ms_i);
	  mr=mr*ms_i);
     Mr)

-- tests for writing in the engine:
/// TEST
R=ZZ[x];
scan(11,i->scan(17,j->(
	       f=i*x;
	       g=j*x;
	       h=chineseRemainder(f,g,11,17);
	       print(h,i*j))));

h=chineseRemainder(180_R,0*x,23,17*19)
180 %23
h % (23*(17*19))
h %23
h %(17*19)
-- imitate chinese remainder:
a=0;
b=180;
m=23;
n=17*19;
(g,um,vn)=toSequence gcdCoefficients(m,n)
um=um*m
vn=vn*n
mn=m*n
result=um*b+vn*a
result % mn
result % 23
result % (17*19)

viewHelp gcd

	       	       )))

///

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
 
reduceViaPrimes=(I,primes,RZ)->(
     apply(primes,p->(
	        Sp:=(ZZ/p)(monoid ring I);
     	  	phi:=map(Sp,ring I, vars Sp);
     	  	Ip:=phi(I);
	  	print("p="|toString(p));
          	time sub(gens gb Ip,RZ))))


majorityRule=(Gs,primes)->(
     GLeadTerms:=apply(Gs, g-> flatten entries leadTerm g);
     tGLeadTerms:=tally GLeadTerms;
     maxVal:=max values tGLeadTerms;
     if maxVal==#primes then (
         (Gs,primes))
     else    
         (
	    L0:=select(1,GLeadTerms,g->tGLeadTerms#g==maxVal);
            pos:=positions(GLeadTerms,g->g==L0_0);
 	    << "badprimes:" << sort toList(set primes - set (primes_pos)) << endl;
	    (Gs_pos,primes_pos)
	 )
     )

reconstructFromCollection=(I,primes,RZ)->(
     Gs:=reduceViaPrimes(I,primes,RZ);
     GsAndPrimes:=majorityRule(Gs,primes);
     )


modGb=(I,primes)->(
     RZ:=ZZ(monoid ring I);
     query:=(p)->(
     	  Sp:=(ZZ/p)(monoid ring I);
     	  phi:=map(Sp,ring I, vars Sp);
     	  Ip:=phi(I);
          sub(gens gb Ip,RZ));
     reconstruct(query,primes,ring I))       
     
beginDocumentation()
     
  
end

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

TEST ///
-- grapped from symbolicdata.m2 in packages/ExampleIdeals
example1=(kk)->(
     R=kk[a,b,x,y,z,u,v,w, MonomialOrder=>Lex];
     ideal"136z-136,  
     -240a+112y+420z-64v,  
     66az+78zv-1056a+90x+336y-90u,  
     -162a2+50ay+180az+55zu-284av+60yv-112b+260x+70w,  
     28azv-648a2+36bx+128ay+36bz-300au+40yu+44xv+192w,  
     15azu-162a2v+18ayv-312ab+84ax+24by+27xu+24aw+30vw,  
     6abz-162a2u+8ayu+10axv+14bx+48aw+16uw,  
     -162a2b+2aby+3axu+4avw+6bw");
I=example1(QQ);
--IQQ=gens gb I;
primes=reverse(select(toList(30000..32000),i->isPrime i));
primes2=primes_{0..20}
--primes2={2,5}|select(toList(101..200),i->isPrime i);
--primes2=primes_{0..10}
RZ=ZZ(monoid R);
--product primes2
--a=random(100000..100000)
--b=random(100000..100000)
--R=QQ[x];
--I=ideal(a*x+b*x^2);
time Gs=reduceViaPrimes(I,primes2,RZ);
GoodGsAndps=majorityRule(Gs,primes2);
#(GoodGsAndps#1)==#primes2
time ICRA=chineseRemainder GoodGsAndps
time ILifted=rationalConversion(ICRA,product GoodGsAndps#1,ring I)
ITest=ideal apply(flatten entries ILifted, f-> myReduce(f,primes_11,RZ));
netList flatten entries (gens gb sub(I,Rp) - sub(ILifted,Rp))
(flatten entries gens gb sub(I,Rp))_{0}-(flatten entries sub(ILifted,Rp))_{0}
Rp=(ZZ/primes_11)(monoid R);
time see ideal(gens gb sub(I,Rp) - sub(ILifted,Rp))


tally apply(Gs, g-> flatten entries leadTerm g)
factor product apply(flatten entries leadTerm gens I, f-> leadCoefficient(f))

time Imod= ideal modGb(I,primes);
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
 
example1=(kk)->(
     R=kk[a,b,x,y,z,u,v,w, MonomialOrder=>Lex];
     ideal"136z-136,  
     -240a+112y+420z-64v,  
     66az+78zv-1056a+90x+336y-90u,  
     -162a2+50ay+180az+55zu-284av+60yv-112b+260x+70w,  
     28azv-648a2+36bx+128ay+36bz-300au+40yu+44xv+192w,  
     15azu-162a2v+18ayv-312ab+84ax+24by+27xu+24aw+30vw,  
     6abz-162a2u+8ayu+10axv+14bx+48aw+16uw,  
     -162a2b+2aby+3axu+4avw+6bw")

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
uninstallPackage"ModularGB"
installPackage"ModularGB";
 loadPackage"ModularGB";
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

p=5*11
apply(p, i-> sub(i,ZZ/p))
apply(p,i->if i>(p//2) then i-p else i)

