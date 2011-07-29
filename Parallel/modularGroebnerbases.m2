-- this should be implemented in the engine in order to speed things up:
chineseRemainder=(a,m)->(
     M:=1;
     N:=0;
     xtmp:=0;
     scan(m,c->M=M*c);
     scan(0..(length m-1),i->(
	       N=sub(M/m_i,ZZ);  
	       xtmp=xtmp+a_i*(gcdCoefficients(m_i,N))_2*N;
	       ));
     xtmp=xtmp%M;
     if xtmp>floor(M/2) then (xtmp-M,M) else (xtmp,M))

-- this should also be implemented in the engine to extend "lift" to the 
-- cases of modular arithmetic w.r.t. composite numbers
ratConvert=(c, m) -> (
     a1 := m; 
     a2 := c;
     u1 := 0;
     u2 := 1;
     q  := 0;
     h  := 0;
     ret:= 0;
     while ( (u2^2 < m/2) and (a2^2 >= m/2)) do (
	  q  = a1//a2;
	  a1 = a1 - q*a2;
	  u1 = u1 - q*u2;
	  h = a1;  a1 = a2; a2 =h;
	  h = u1;  u1 = u2; u2 =h;
	  );
     if  (u2^2 >= m/2) then (ret = {0};) else (
     if  (a2^2 < m/2) then (ret = {a2,u2};));
     ret)

ratConvert'=(m,p)->(
     r:=ratConvert(m,p); 
     if #r==1 then m else r_0/r_1)

liftMatrix=(m,p)->(matrix applyTable(entries m,f->ratConvert'(f,p)))

combineMatrix=(M,N)->(
     (m,p):=M;
     (n,q):=N;
     print("in combine:");
     time m=entries m;
     time n=entries n;
     -- the following loop seems to be the bottle-neck:
     print(#m-1,#(m_0)-1);
     time X:=matrix for i from 0 to #m-1 list 
                       for j from 0 to #(m_0)-1 list
		          if m#i#j==0 and n#i#j==0 then 0 else  
	                     (chineseRemainder({m#i#j,n#i#j},{p,q}))_0;
     (X,p*q))

reconstruct=(f,primes)->(
      mZZ:=(f(primes_0),primes_0);
      print("lift:");
      time mQQ:=liftMatrix(mZZ);
      for i from 1 to #primes-1 do (
	   mZZ':=(f(primes_i),primes_i);
	   print("combine:");
	   time mZZ=combineMatrix(mZZ,mZZ');
	   oldmQQ:=mQQ;
	   print("lift:");
	   time mQQ=liftMatrix(mZZ);
	   if mQQ== oldmQQ then (
		<<"match at "<< i << endl;
		return mQQ);
	   );
      <<"d'oh! could not lift. Use more primes" << endl;
      )

modGb=(I,primes)->(
     query:=(p)->(
     	  Sp:=ZZ/p[gens ring I];
     	  phi:=map(Sp,ring I, vars Sp);
     	  Ip:=phi(I);
     	  gens gb Ip);
     monoms:=sub((coefficients(query(primes_0)))_0,ring I);
     -- here we assume that primes_0 is not a bad reduction
     f:=(p)->(
	  cfs:=coefficients(query(p));
     	  if sub(cfs_0,ring I)!=sub(monoms,ring I) then error "d'oh! Bad reduction happened!" else
	  sub(cfs_1,ZZ));
     cfsQQ:=reconstruct(f,primes);
     monoms*cfsQQ)        
end;     	   
         
restart;
load"modularGroebnerbases.m2";
#(primes=reverse(select(toList(30000..32000),i->isPrime i)))
R=QQ[x_0..x_5];
I=ideal random(R^1,R^{4:-3});
time gens gb I;
Imod= ideal modGb(I,primes);
s1=netList Imod_*
s2=netList apply((ideal gens gb I)_*,f->1/(leadCoefficient(f)) * f)
s1==s2

combine
ra



17/101*I_0
coefficients(gens I)
query=(p)->(
     Sp:=ZZ/p[gens ring I];
     phi:=map(Sp,ring I, vars Sp);
     Ip:=phi(I);
     sub(gens gb Ip, RZ)) 

query(1009)     
f=(p)->(sub((coefficients(query(p)))_1,ZZ))


     
     
reconstruct(f,primes)
f(1009)
reconstruct(f,primes)
for 
m0=sub(sub(m,ZZ/primes_0),ZZ)
m1=sub(sub(m,ZZ/primes_1),ZZ)
liftMatrix(m0,primes_0)
liftMatrix(m1,primes_1)
liftMatrix(combineMat((m0,primes_0),(m1,primes_1)))

	   m1
	    chineseRemainder({3,8},{5,7})
sqrt(primes_0)/2
     
time bases=apply(primes,p->time(

time re=reconstruct(bases,primes);

bases_0
m=re_1
coeffs=coefficients(re_0)
clifted=matrix apply(rank target coeffs_1,i->
            apply(rank source coeffs_1,j->(
		       r:=ratConvert(sub(coeffs_1_(i,j),ZZ),m);
		       if #r!=1 then r_0/r_1 else -1)))
mingens ideal(coeffs_0* clifted)
mingens ideal(gb0_(0,nmbr))
matrix apply(rank target re_0, i-> apply(rank source re_0, j-> ratConvert(sub(((coefficients re_0)_1)_(i,j),ZZ),re_1)))

ratConvert(((coefficients re_0)_1)_(0,0),re)
coefficients(gbs_0)
--gbs
Ms=toSequence apply(gbs,g->contract(basis(degree(gbs_0)_(0,0),ring g),g_(0,0)))
reconstruct(Ms,ps)
     	  apply(gbp, g->flatten entries sub(contract(basis(degree g, Stmp),g),ZZ))

coefficients (gbs_0);	  
oo
viewHelp coefficients


6 % 11
6 > 11/2
6- 11
p=101

tally apply({3,5,7,11,101},p->p==#(ceiling(-p/2)..floor(p/2)))
M1=random(ZZ^200,ZZ^200);
M2=random(ZZ^200,ZZ^200);
time matrix apply(200,i->apply(200,j-> gcd(M1_(i,j),M2_(i,j))));
time map(ZZ^200,ZZ^200, (i,j)-> gcd(M1_(i,j),M2_(i,j)));
m1=entries M1;
m2=entries M2;
time X=matrix for i from 0 to 199 list for j from 0 to 199 list gcd(m1#i#j,m2#i#j);
   
		      viewHelp lift
