chineseRemainder=(a,m)->(
     M:=1;
     N:=0;
     xtmp:=0;
     apply(m,c->M=M*c);
     apply(0..(length m-1),i->(
	       N=sub(M/m_i,ZZ);  
	       xtmp=xtmp+a_i*(gcdCoefficients(m_i,N))_2*N;
	       ));
      (xtmp%M,M));

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

reconstruct=method()
-- takes a list of groebner basis over finite fields and tries to reconstruct them
reconstruct(List,List):=(bases,primes)->(
     coeffs=apply(bases, m-> coefficients m);
     if not #unique apply(coeffs,c->c_0)==1 then error "not all gb's are of the same shape";
     M:=matrix apply(rank target coeffs_0_1,i->
	         apply(rank source coeffs_0_1,j->(chineseRemainder(apply(#coeffs,k->sub(coeffs_k_1_(i,j),ZZ)),primes))_0));
     (coeffs_0_0*M,product primes))
     
end;


restart;
load"modularGroebnerbases.m2"
allowableThreads=2
R=QQ[x_0..x_2];
I=ideal random(R^1,R^{3:-3});
--time gens gb I; -- 6.46757 seconds
primes=(select(toList(100..200),i->isPrime i))_{0..5}

time bases=apply(primes,p->time(
	  Stmp=ZZ/p[x_0..x_2];
	  phi1=map(Stmp,R,vars Stmp);
	  sub(gens gb phi1(I),R)));
time re=reconstruct(bases,primes);
re
((coefficients re_0)_1)_(0,0)
coefficients(gbs_0)
--gbs
Ms=toSequence apply(gbs,g->contract(basis(degree(gbs_0)_(0,0),ring g),g_(0,0)))
reconstruct(Ms,ps)
     	  apply(gbp, g->flatten entries sub(contract(basis(degree g, Stmp),g),ZZ))

coefficients (gbs_0);	  
oo
viewHelp coefficients
