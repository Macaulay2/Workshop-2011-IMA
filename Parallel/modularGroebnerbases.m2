chineseRemainder=(a,m)->(
     M:=1;
     N:=0;
     xtmp:=0;
     apply(m,c->M=M*c);
     apply(0..(length m-1),i->(
	       N=sub(M/m_i,ZZ);  
	       xtmp=xtmp+a_i*(gcdCoefficients(m_i,N))_2*N;
	       ));
     xtmp=xtmp%M;
     if xtmp>floor(M/2) then (xtmp-M,M) else (xtmp,M))

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

liftMatrix=(m,p)->( matrix applyTable(entries m,f->ratConvert'(f,p)))

combineMatrix=(M,N)->(
     (m,p):=M;
     (n,q):=N;
     m=entries m;
     n=entries n;
     X:=matrix for i from 0 to #m-1 list 
                   for j from 0 to #(m_0)-1 list 
	               (chineseRemainder({m#i#j,n#i#j},{p,q}))_0;
     (X,p*q))



reconstruct=(f,primes)->(
      mZZ:=(f(primes_0),primes_0);
      time mQQ:=liftMatrix(mZZ);
      for i from 1 to #primes-1 do (
	   mZZ':=(f(primes_i),primes_i);
	   mZZ=combineMatrix(mZZ,mZZ');
	   oldmQQ:=mQQ;
	   mQQ=liftMatrix(mZZ);
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
         
    
reconstruct=method()
-- takes a list of groebner basis over finite fields and tries to reconstruct them
reconstruct(List,List):=(bases,primes)->(
     coeffs:=apply(bases, m-> coefficients m);
     if not #unique apply(coeffs,c->c_0)==1 then error "not all gb's are of the same shape";
     M:=matrix apply(rank target coeffs_0_1,i->
	         apply(rank source coeffs_0_1,j->(chineseRemainder(apply(#coeffs,k->sub(coeffs_k_1_(i,j),ZZ)),primes))_0));
     (coeffs_0_0*M,product primes))
     
end;


restart;
path=path_{1..#path-1}
load"modularGroebnerbases.m2"
allowableThreads=2
R=QQ[x_0..x_3];
-- vanishing ideal of 
I=ideal random(R^1,R^{2:-2}); 
betti I
time gb0=(gens gb I)
#(primes=(select(toList(30000..32000),i->isPrime i)))
-- time max(apply(flatten entries(coefficients(gb0))_1,f-> abs(sub(f,ZZ))))
redGb=(p)->(
     	  Stmp:=ZZ/p[x_0..x_3];
	  phi1:=map(Stmp,R,vars Stmp);
	  (sub(gens gb phi1(I),R)))

primesPart=primes_{0..10};
gbs=primesPart/redGb;
n=2;
time re=reconstruct(gbs_{0..n-1}, primesPart_{0..n-1});
cfs=coefficients(re_0);
cfs_1
matrix apply(rank target cfs_1,i-> 
            apply(rank source cfs_1,j->(
		 r:=ratConvert(sub(cfs_1_(i,j),QQ),sub(re_1,QQ));
		 if #r==1 then cfs_1_(i,j) else r_0/r_1)))
		 
		 
		 ))
restart;
load"modularGroebnerbases.m2";
#(primes=reverse(select(toList(30000..32000),i->isPrime i)))
R=QQ[a,b,c,d];
I=ideal random(R^1,R^{2:-3})
Imod= ideal modGb(I,primes);
s1=netList Imod_*
s2=netList apply((ideal gens gb I)_*,f->1/(leadCoefficient(f)) * f)
s1==s2



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
