  needsPackage  "MGBInterface"  

R = ZZ/32003[vars(0..15)]
M = genericMatrix(R,a,4,4)
I = permanents(3,M)



end

  restart
  debug needsPackage "PD"
  debug needsPackage "SingularInterface"

  load "PD/example-permanents.m2"
  load "mike-pd.m2"
-------------
-- Trying to improve speed of minprimes of this ideal (18 June 2013, MES).
-- Singular takes only a few minutes on it.
-- Singular arrives at 70 minimal primes
  
  time L = myGB I;
  --time L = MGB I;  -- 5.4 seconds

  -- 1 July 2013: attempt to compute this

  -- now run this until it stops

  time L = trim addInMonomials L;
  time L = trim addSquarefrees L;

  time minprimes(L, Verbosity=>2);

  debug PD
  strat1 = ({Linear,DecomposeMonomials,(Factorization,3)},infinity)
  strat1 = ({Linear,(Factorization,3)},infinity)
  strat = ({strat1, (Birational,infinity)},infinity)
  time minprimes(L, Verbosity=>2, Strategy=>strat);
  
  pdState = createPDState(L);
  time C = splitIdeals({annotatedIdeal(L,{},{},{})}, strat, Verbosity=>2, "PDState"=>pdState);

  
  C = splitIdeals({annotatedIdeal(L,{},{},{})}, strat1, Verbosity=>2, "PDState"=>pdState);
  C = splitIdeals({annotatedIdeal(L,{},{},{})}, (DecomposeMonomials,1), Verbosity=>2, "PDState"=>pdState);

  decompose monomialIdeal select(L_*, f -> size f == 1)
  

  keys pdState#"PrimesSoFar"  
  
  time L1 = {(1,WORKING,L)};
  time L2 = L1/irredPrimes//flatten;
  time L3 = L2/irredPrimes//flatten;
  time L4 = L3/irredPrimes//flatten;
  time L5 = L4/irredPrimes//flatten;
  time L6 = L5/irredPrimes//flatten;
  time L7 = L6/irredPrimes//flatten;
  L7a = select(L7, i -> i#2 != 1);
  #L7a
  time L8 = L7a/irredPrimes//flatten;    
  L8a = select(L8, i -> i#2 != 1);
  time L9 = L8a/irredPrimes//flatten;    
  L9a = select(L9, i -> i#2 != 1);
  time L10 = L9a/irredPrimes//flatten;    
  L10a = select(L10, i -> i#2 != 1);
  time L11 = L10a/irredPrimes//flatten;    
  L11a = select(L11, i -> i#2 != 1);
  time L12 = L11a/irredPrimes//flatten;    
  L12a = select(L12, i -> i#2 != 1);
  
  L0 = {L}
  L1 = time splice for I in L0 list (
      v := findsplitvar I;
      if v === null then I else splitme(I,v)
      );
  L2 = time splice for I in L1 list (
      v := findsplitvar I;
      if v === null then I else splitme(I,v)
      );
  L3 = time splice for I in L2 list (
      v := findsplitvar I;
      if v === null then I else splitme(I,v)
      );
  L4 = time splice for I in L3 list (
      v := findsplitvar I;
      if v === null then I else splitme(I,v)
      );
  L5 = time splice for I in L4 list (
      v := findsplitvar I;
      if v === null then I else splitme(I,v)
      );
  L6 = time splice for I in L5 list (
      v := findsplitvar I;
      if v === null then I else splitme(I,v)
      );
  L7 = time splice for I in L6 list (
      v := findsplitvar I;
      if v === null then I else splitme(I,v)
      );
  L8 = time splice for I in L7 list (
      v := findsplitvar I;
      if v === null then I else splitme(I,v)
      );

  -- now select the ones of codim 8:
  C8 = select(L8, i -> codim i === 8)
  time (L1, L2) = splitme(L, a); -- 
  oo/codim
  ooo/degree

  -- now let's consider C8_7
  C8_7
  (F,G) = indepsets(C8_7, 3)
  L1 = contractit(ideal first F, F#1)
  L2 = saturate(C8_7, L1)

  (codim L1, codim L2)
  degree L1
  degree L2  
  
  -- now do it for L2:
  (F,G) = indepsets(L2, 3)
  L3 = contractit(ideal first F, F#1)
  L4 = saturate(L2, L3)
  degree L3  
  degree L4

  -- now for L4:
  (F,G) = indepsets(L4, 3)
  L5 = contractit(ideal first F, F#1)
  L6 = saturate(L4,L5)
  degree L5
  degree L6

  -- now for L6:
  (F,G) = indepsets(L6, 3)
  L7 = contractit(ideal first F, F#1)
  L8 = saturate(L6,L7)
  degree L7
  degree L8

  -- now for L8:
  (F,G) = indepsets(L8, 3)
  L9 = contractit(ideal first F, F#1)
  L10 = saturate(L8,L9)
  degree L9
  degree L10

  C = splitIdeal(L, Strategy=>{DecomposeMonomials}, Verbosity=>2);
  #C  -- 53
  positions(C, i -> codim i === 8)
  C8 = select(C, i -> codim i === 8);
  #C8 -- 23
  select(C8, i -> numgens ideal i == 8)
  minprimes(C8_0 . Ideal, Verbosity=>2)  

  I = C8_0 . Ideal
  minprimes(I, Strategy=>{(IndependentSet, infinity)}, Verbosity => 2)
  time minprimes(ideal C8_1, Strategy=>{(IndependentSet, infinity)}, Verbosity => 2)
-- minprimes(L, Verbosity=>2); -- interrupted it after 702 primes found
  -- in a place where pdState is defined
  L8 = pdState#"PrimesSoFar"#8 /last;
  L9 = pdState#"PrimesSoFar"#9 /last;
  L10 = pdState#"PrimesSoFar"#10 /last;
  L11 = pdState#"PrimesSoFar"#11 /last;
  L12 = pdState#"PrimesSoFar"#12 /last;
  time selectMinimalIdeals join(L8,L9,L10,L11);  
  -- how bad is it to do indep sets right away?
  basevars = support first independentSets L
 (S, SF) = makeFiberRings(basevars,ring L)  
 hf = poincare L
 JS := S.cache#"RtoS" L;
 time gb(JS, Hilbert=>hf);
 (JSF, coeffs) := minimalizeOverFrac(JS, SF);
 
  M = L_*/leadTerm//monomialIdeal;
  (L1, maxdeg) = divideByVariable(gens L, p);
  L1 = ideal L1;
  time gens gb L1;
  L2 = trim L1;
  time gens gb L2;
  time L3 = L : L2;
  codim L2
  codim M -- 8
  degree M -- ouch!!  but using hilbertSeries, get 588...

  C = decompose radical monomialIdeal select(L_*, f -> size f == 1)
  C1 = apply(C, P -> trim(P + I));
  cnt = 0
  C1 = apply(C1, P -> (cnt = cnt+1; (codim P, cnt, P)))
  C1 = sort C1
  C1 = C1/(p -> last p)

  time minprimes(C1_0, Strategy=>NoBirationalStrat, Verbosity=>2);
  time minprimes(C1_1, Strategy=>NoBirationalStrat, Verbosity=>2);  -- 49 primes, 10.7 sec
  time minprimes(C1_2, Strategy=>NoBirationalStrat, Verbosity=>2);  -- 1.7 sec, 26 primes
  time minprimes(C1_4, Strategy=>NoBirationalStrat, Verbosity=>2);  -- 
  time for i from 23 to #C1-1 list (
      << "DOING " << i << endl;
      time minprimes(C1_i, Strategy=>NoBirationalStrat, Verbosity=>2);
      )

  strat = ({Linear, DecomposeMonomials, Factorization, IndependentSet}, infinity)
  time for i from 20 to #C1-1 list (
      << "DOING " << i << endl;
      time minprimes(C1_i, Strategy=>strat, Verbosity=>2);
      )

  facs = (factors G)/last 
  Jsat = J
  for f in facs do (
      time Jsat = if index f =!= null then mySat(Jsat, f) else saturate(Jsat, f)
      )
  time J : Jsat;
-----------------------
-- saturate examples --  
-----------------------
  R = ZZ/32003[vars(0..15)]
  J = ideal(h*k*n+g*l*n+h*j*o+f*l*o+g*j*p+f*k*p,h*k*m+g*l*m+h*i*o+e*l*o+g*i*p+e*k*p,h*j*m+f*l*m+h*i*n+e*l*n+f*i*p+e*j*p,g*j*m+f*k*m+g*i*n+e*k*n+f*i*o+e*j*o,f*g*i*k*m*n+e*f*k^2*m*n+e*g*i*k*n^2+e^2*k^2*n^2+f^2*i*k*m*o+e*f*j*k*m*o+f*g*i^2*n*o+e*g*i*j*n*o+e*f*i*k*n*o+e^2*j*k*n*o+f^2*i^2*o^2+e*f*i*j*o^2,f*g*h^2*i^2*j*k+e*g*h^2*i*j^2*k+e*f*h^2*i*j*k^2+f*g^2*h*i^2*j*l+e*g^2*h*i*j^2*l+f^2*g*h*i^2*k*l+e^2*g*h*j^2*k*l+e*f^2*h*i*k^2*l+e^2*f*h*j*k^2*l+e*f*g^2*i*j*l^2+e*f^2*g*i*k*l^2+e^2*f*g*j*k*l^2);
  G = -e*f^2*g*h^4*i^3*j^3*l*p+e^2*f*g*h^4*i^2*j^4*l*p-2*e*f^3*g*h^3*i^3*j^2*l^2*p+2*e^3*f*g*h^3*i*j^4*l^2*p-e*f^4*g*h^2*i^3*j*l^3*p-2*e^2*f^3*g*h^2*i^2*j^2*l^3*p+2*e^3*f^2*g*h^2*i*j^3*l^3*p+e^4*f*g*h^2*j^4*l^3*p-e^2*f^4*g*h*i^2*j*l^4*p+e^4*f^2*g*h*j^3*l^4*p;
  Jsat = saturate(J,G);
  J2 = J : Jsat;

  -- in ideal C1_4
  R = ZZ/32003[vars(0..15)]
  J = ideal(d*k*n+c*l*n+d*j*o+b*l*o+c*j*p+b*k*p,d*k*m+c*l*m+d*i*o+a*l*o+c*i*p+a*k*p,d*j*m+b*l*m+d*i*n+a*l*n+b*i*p+a*j*p,c*j*m+b*k*m+c*i*n+a*k*n+b*i*o+a*j*o,b*c*i*k*m*n+a*b*k^2*m*n+a*c*i*k*n^2+a^2*k^2*n^2+b^2*i*k*m*o+a*b*j*k*m*o+b*c*i^2*n*o+a*c*i*j*n*o+a*b*i*k*n*o+a^2*j*k*n*o+b^2*i^2*o^2+a*b*i*j*o^2,b*c*d^2*i^2*j*k+a*c*d^2*i*j^2*k+a*b*d^2*i*j*k^2+b*c^2*d*i^2*j*l+a*c^2*d*i*j^2*l+b^2*c*d*i^2*k*l+a^2*c*d*j^2*k*l+a*b^2*d*i*k^2*l+a^2*b*d*j*k^2*l+a*b*c^2*i*j*l^2+a*b^2*c*i*k*l^2+a^2*b*c*j*k*l^2);
  G = -a*b^2*c*d^4*i^3*j^3*l*p+a^2*b*c*d^4*i^2*j^4*l*p-2*a*b^3*c*d^3*i^3*j^2*l^2*p+2*a^3*b*c*d^3*i*j^4*l^2*p-a*b^4*c*d^2*i^3*j*l^3*p-2*a^2*b^3*c*d^2*i^2*j^2*l^3*p+2*a^3*b^2*c*d^2*i*j^3*l^3*p+a^4*b*c*d^2*j^4*l^3*p-a^2*b^4*c*d*i^2*j*l^4*p+a^4*b^2*c*d*j^3*l^4*p;
  Jsat = saturate(J,G);
  J2 = J : Jsat;

  -- above example from C1_4 is this:
  R = ZZ/32003[a, b, c, d, i, j, k, l, m, n, o, p]
  I = ideal(d*k*n+c*l*n+d*j*o+b*l*o+c*j*p+b*k*p,d*k*m+c*l*m+d*i*o+a*l*o+c*i*p+a*k*p,d*j*m+b*l*m+d*i*n+a*l*n+b*i*p+a*j*p,c*j*m+b*k*m+c*i*n+a*k*n+b*i*o+a*j*o,b*c*i*k*m*n+a*b*k^2*m*n+a*c*i*k*n^2+a^2*k^2*n^2+b^2*i*k*m*o+a*b*j*k*m*o+b*c*i^2*n*o+a*c*i*j*n*o+a*b*i*k*n*o+a^2*j*k*n*o+b^2*i^2*o^2+a*b*i*j*o^2,b*c*d^2*i^2*j*k+a*c*d^2*i*j^2*k+a*b*d^2*i*j*k^2+b*c^2*d*i^2*j*l+a*c^2*d*i*j^2*l+b^2*c*d*i^2*k*l+a^2*c*d*j^2*k*l+a*b^2*d*i*k^2*l+a^2*b*d*j*k^2*l+a*b*c^2*i*j*l^2+a*b^2*c*i*k*l^2+a^2*b*c*j*k*l^2);
  time minprimes(I, Verbosity=>2);  
  ann Ext^4(comodule I, ring I) == I -- this is true, so this I is equidimensional, degree I == 77, codim I == 4.
  I1 = I : (k*n + j*o)
  I2 = I : I1
  intersect(I1, I2) == I -- true, as it should be, since I is equidimensional
  
  -- in C1_14  
  J = ideal(d*g*n+c*h*n+d*f*o+b*h*o+c*f*p+b*g*p,d*g*m+c*h*m+d*e*o+a*h*o+c*e*p+a*g*p,d*f*m+b*h*m+d*e*n+a*h*n+b*e*p+a*f*p,c*f*m+b*g*m+c*e*n+a*g*n+b*e*o+a*f*o,b*c*e*g*m*n+a*b*g^2*m*n+a*c*e*g*n^2+a^2*g^2*n^2+b^2*e*g*m*o+a*b*f*g*m*o+b*c*e^2*n*o+a*c*e*f*n*o+a*b*e*g*n*o+a^2*f*g*n*o+b^2*e^2*o^2+a*b*e*f*o^2,b*c*d^2*e^2*f*g+a*c*d^2*e*f^2*g+a*b*d^2*e*f*g^2+b*c^2*d*e^2*f*h+a*c^2*d*e*f^2*h+b^2*c*d*e^2*g*h+a^2*c*d*f^2*g*h+a*b^2*d*e*g^2*h+a^2*b*d*f*g^2*h+a*b*c^2*e*f*h^2+a*b^2*c*e*g*h^2+a^2*b*c*f*g*h^2)
  G = -a*b^2*c*d^4*e^3*f^3*h*p+a^2*b*c*d^4*e^2*f^4*h*p-2*a*b^3*c*d^3*e^3*f^2*h^2*p+2*a^3*b*c*d^3*e*f^4*h^2*p-a*b^4*c*d^2*e^3*f*h^3*p-2*a^2*b^3*c*d^2*e^2*f^2*h^3*p+2*a^3*b^2*c*d^2*e*f^3*h^3*p+a^4*b*c*d^2*f^4*h^3*p-a^2*b^4*c*d*e^2*f*h^4*p+a^4*b^2*c*d*f^3*h^4*p;
  Jsat = saturate(J,G);
  J2 = J : Jsat;

  -- in C1_16, in contractToPolynomialRing  
  newIinR = ideal(m*c*h+m*d*g+o*a*h+o*d*e+a*g*p+c*e*p,k*a*d*g*h*p-k*c*d*e*h*p+o*a*d*g*h*l-o*c*d*e*h*l-a*c*g*h*l*p+a*d*g^2*l*p-c^2*e*h*l*p+c*d*e*g*l*p,o^2*a^2*d*g*h^2-o^2*a*c*d*e*h^2+o^2*a*d^2*e*g*h-o^2*c*d^2*e^2*h-o*a^2*c*g*h^2*p+o*a^2*d*g^2*h*p-o*a*c^2*e*h^2*p+o*a*d^2*e*g^2*p-o*c^2*d*e^2*h*p+o*c*d^2*e^2*g*p-a^2*c*g^2*h*p^2-a*c^2*e*g*h*p^2+a*c*d*e*g^2*p^2+c^2*d*e^2*g*p^2,i*a*c*d*g*h^2*p+i*a*d^2*g^2*h*p-i*c^2*d*e*h^2*p-i*c*d^2*e*g*h*p-o*a^2*d*g*h^2*l+o*a*c*d*e*h^2*l-o*a*d^2*e*g*h*l+o*c*d^2*e^2*h*l+a^2*c*g*h^2*l*p+a*c^2*e*h^2*l*p-a*d^2*e*g^2*l*p-c*d^2*e^2*g*l*p)  
  denomList = {h, d, a*h + d*e, a*g - c*e, c*h + d*g, p}
  Isat = newIinR
  for den in denomList do Isat = saturate(Isat, den);

  -- in C1_22
  J = ideal(h*k*n+g*l*n+h*j*o+f*l*o,d*k*n+c*l*n+d*j*o+b*l*o,d*g*n+c*h*n+d*f*o+b*h*o,h*k*m+g*l*m+h*i*o+e*l*o,d*k*m+c*l*m+d*i*o+a*l*o,h*j*m+f*l*m+h*i*n+e*l*n,g*j*m+f*k*m+g*i*n+e*k*n+f*i*o+e*j*o,d*j*m+b*l*m+d*i*n+a*l*n,c*j*m+b*k*m+c*i*n+a*k*n+b*i*o+a*j*o,d*g*m+c*h*m+d*e*o+a*h*o,d*f*m+b*h*m+d*e*n+a*h*n,c*f*m+b*g*m+c*e*n+a*g*n+b*e*o+a*f*o,d*g*j+c*h*j+d*f*k+b*h*k+c*f*l+b*g*l,d*g*i+c*h*i+d*e*k+a*h*k+c*e*l+a*g*l,d*f*i+b*h*i+d*e*j+a*h*j+b*e*l+a*f*l,c*f*i+b*g*i+c*e*j+a*g*j+b*e*k+a*f*k,a^2*g*j*l*o,c*e^2*j*l*o,b*f*g*i*l*o+c*e*f*j*l*o+a*f^2*k*l*o,b^2*g*i*l*o,b*e*f*i*l*o+a*e*f*j*l*o,a*b*f*i*l*o+a*b*e*j*l*o,b*c*e*f*l*o+a*b*f*g*l*o,a*c*e*f*l*o+a*b*e*g*l*o,a*b*e*f*l*o,b*e*g*h*j*o-a*f*g*h*j*o+a*f^2*h*k*o-c*e*f^2*l*o+b*e*f*g*l*o,a*b*g*h*j*o+a*b*f*g*l*o,a^2*g*h*j*o-a*b*e*g*l*o,c*e^2*h*j*o-a*e*g*h*j*o+c*e^2*f*l*o-a*e*f*g*l*o,b*e^2*h*j*o-a*e*f*h*j*o+b*e^2*f*l*o-a*e*f^2*l*o,c*d*e*h*j*o+a*c*h^2*j*o+a*c*f*h*l*o,b*d*e*h*j*o+a*b*h^2*j*o,a*d*e*h*j*o+a^2*h^2*j*o+a^2*f*h*l*o,a*b*e*h*j*o,b*c*d*e*j*o+a*b*c*h*j*o+a*b*d*f*k*o,a*c*d*e*j*o+a^2*c*h*j*o+a^2*d*f*k*o+a*b*c*e*l*o+a^2*c*f*l*o-a^2*b*g*l*o,a*b*d*e*j*o+a^2*b*h*j*o+a*b^2*e*l*o,b*c*e*g*i*j+a*b*g^2*i*j+a*c*e*g*j^2+a^2*g^2*j^2+b^2*e*g*i*k+a*b*f*g*i*k+b*c*e^2*j*k+a*c*e*f*j*k+a*b*e*g*j*k+a^2*f*g*j*k+b^2*e^2*k^2+a*b*e*f*k^2,b*h*i^2*j*o^2-a*h*i*j^2*o^2-a*f*i*j*l*o^2,a*g^2*j^2*l*o-a*f^2*k^2*l*o,a*c*g*j^2*l*o-a*b*g*j*k*l*o,a*g^2*i*j*l*o-a*e*g*j*k*l*o,a*c*g*i*j*l*o,b*d*f^2*k^2*o+b^2*f*h*k^2*o-b*c*f*g*j*l*o+b*c*f^2*k*l*o+b^2*f*g*k*l*o,a*d*e^2*k^2*o+a^2*e*h*k^2*o-a*c*e*g*i*l*o+a*c*e^2*k*l*o+a^2*e*g*k*l*o,e*f*h*i*j*k*o-e*f*g*i*j*l*o+e*f^2*i*k*l*o+e^2*f*j*k*l*o,b*f*h*i*j*k*o-a*f^2*j*k*l*o,a*e*h*i*j*k*o+a*e*f*i*k*l*o,b^2*h*i*j*k*o+b^2*f*i*k*l*o-a*b*f*j*k*l*o,a^2*h*i*j*k*o+a^2*f*i*k*l*o+a^2*e*j*k*l*o,a*b*d*i*j*k*o-a*b*c*i*j*l*o+a*b^2*i*k*l*o+a^2*b*j*k*l*o,a*e*h*i*j^2*o+a*e^2*j^2*l*o,a^2*h*i*j^2*o,b*f*h*i^2*j*o-a*e*f*j^2*l*o,b^2*h*i^2*j*o,a*b*d*e*f*g*o-a*b*c*e*f*h*o+a*b^2*e*g*h*o+a^2*b*f*g*h*o,a*d*e^2*j^2*n+a^2*e*h*j^2*n-a*b*e*f*i*l*n+a*b*e^2*j*l*n+a^2*e*f*j*l*n,b*c*d^2*e^2*f*g+a*c*d^2*e*f^2*g+a*b*d^2*e*f*g^2+b*c^2*d*e^2*f*h+a*c^2*d*e*f^2*h+b^2*c*d*e^2*g*h+a^2*c*d*f^2*g*h+a*b^2*d*e*g^2*h+a^2*b*d*f*g^2*h+a*b*c^2*e*f*h^2+a*b^2*c*e*g*h^2+a^2*b*c*f*g*h^2);
  G = -a*b^2*c*d^4*e^4*f^3*h*l+a^2*b*c*d^4*e^3*f^4*h*l-2*a*b^3*c*d^3*e^4*f^2*h^2*l+2*a^3*b*c*d^3*e^2*f^4*h^2*l-a*b^4*c*d^2*e^4*f*h^3*l-2*a^2*b^3*c*d^2*e^3*f^2*h^3*l+2*a^3*b^2*c*d^2*e^2*f^3*h^3*l+a^4*b*c*d^2*e*f^4*h^3*l-a^2*b^4*c*d*e^3*f*h^4*l+a^4*b^2*c*d*e*f^3*h^4*l;
  Jsat = saturate(J,G);
  J2 = J : Jsat;
-------------
  time minprimes I

  J = ideal gens gb I;
  (C,backToOriginalRing) = time minprimes(J,Strategy=>{DecomposeMonomials, Linear,Factorization,DecomposeMonomials,Linear,Factorization});  
  C1 = select(C, c -> (c.?isPrime and c.isPrime === "UNKNOWN") or numgens c.Ideal > 1)
  time gens gb I;
  G = flatten entries oo;

  G/size//tally  
  I1 = ideal radical monomialIdeal select(G, g -> size g === 1)
  primaryDecomposition oo
  J = I + I1;  
  gens gb J;
  G = flatten entries oo;
  G/size//tally  
  I2 = ideal radical monomialIdeal select(G, g -> size g === 1)
  J = J + I2;
  gens gb J    ;

  G = flatten entries oo;
  G/size//tally  
  I3 = ideal radical monomialIdeal select(G, g -> size g === 1)
  J = J + I3;
  gens gb J;

  G = flatten entries oo;
  G/size//tally  
  I4 = ideal radical monomialIdeal select(G, g -> size g === 1)
  J = J + I4;

  gens gb J;
  G = flatten entries oo;
  G/size//tally  
  I4 = ideal radical monomialIdeal select(G, g -> size g === 1)
  J = J + I4;

  betti J  
  time C = birationalSplit J;
  time minprimes(J, Verbosity=>1);
  
  
----------------------
-- 
R = ZZ/32003[vars(0..15)]
I = ideal(m,i,e,a,h*k*n+g*l*n+h*j*o+f*l*o+g*j*p+f*k*p,d*k*n+c*l*n+d*j*o+b*l*o+c*j*p+b*k*p,d*g*n+c*h*n+d*f*o+b*h*o+c*f*p+b*g*p,d*g*j+c*h*j+d*f*k+b*h*k+c*f*l+b*g*l,g*h*j*l*n*o+f*g*l^2*n*o+f*h*j*l*o^2+f^2*l^2*o^2+g^2*j*l*n*p+f*g*k*l*n*p+g*h*j^2*o*p+f*h*j*k*o*p+f*g*j*l*o*p+f^2*k*l*o*p+g^2*j^2*p^2+f*g*j*k*p^2,c*d*f*h*n*o+b*c*h^2*n*o+b*d*f*h*o^2+b^2*h^2*o^2+c^2*f*h*n*p+b*c*g*h*n*p+c*d*f^2*o*p+b*d*f*g*o*p+b*c*f*h*o*p+b^2*g*h*o*p+c^2*f^2*p^2+b*c*f*g*p^2,c*d*f*h*j*k+b*c*h^2*j*k+b*d*f*h*k^2+b^2*h^2*k^2+c^2*f*h*j*l+b*c*g*h*j*l+c*d*f^2*k*l+b*d*f*g*k*l+b*c*f*h*k*l+b^2*g*h*k*l+c^2*f^2*l^2+b*c*f*g*l^2,d^2*g*h*k*l*o^2+c*d*h^2*k*l*o^2+c*d*g*h*l^2*o^2+d^2*g*h*k^2*o*p+c*d*h^2*k^2*o*p+d^2*g^2*k*l*o*p+c^2*h^2*k*l*o*p+c*d*g^2*l^2*o*p+c^2*g*h*l^2*o*p+c*d*g*h*k^2*p^2+c*d*g^2*k*l*p^2+c^2*g*h*k*l*p^2,c^2*f*g*j*k*n^2+b*c*g^2*j*k*n^2+b*c*f*g*k^2*n^2+c^2*f*g*j^2*n*o+b*c*g^2*j^2*n*o+c^2*f^2*j*k*n*o+b^2*g^2*j*k*n*o+b*c*f^2*k^2*n*o+b^2*f*g*k^2*n*o+b*c*f*g*j^2*o^2+b*c*f^2*j*k*o^2+b^2*f*g*j*k*o^2)
time minprimes(I, Strategy=>NoBirationalStrat, Verbosity=>2);

-- problem: how to quickly go from I, linears to the ideal in the ring including these linear vars?
linears = {(p,c*j+b*k,d*k*n+c*l*n+d*j*o+b*l*o+c*j*p+b*k*p), (k,d*m*n,d*k*m*n+c*l*m*n+d*j*m*o+b*l*m*o+d*i*n*o+a*l*n*o), (b,a*i*l*m*o,16001*c*d*i*j*m^2-16001*a*c*j*l*m^2+16001*c*d*i^2*m*n-16001*a*c*i*l*m*n-16001*a*d*i*j*m*o+a*b*i*l*m*o-16001*a^2*j*l*m*o-16001*a*d*i^2*n*o-16001*a^2*i*l*n*o)}
I = ideal(c^2*d^2*i^2*j^2*m^4-2*a*c^2*d*i*j^2*l*m^4+a^2*c^2*j^2*l^2*m^4+2*c^2*d^2*i^3*j*m^3*n-2*a*c^2*d*i^2*j*l*m^3*n+c^2*d^2*i^4*m^2*n^2-a^2*c^2*i^2*l^2*m^2*n^2-2*a^2*c*d*i*j^2*l*m^3*o+2*a^3*c*j^2*l^2*m^3*o-2*a*c*d^2*i^3*j*m^2*n*o-4*a^2*c*d*i^2*j*l*m^2*n*o-2*a^3*c*i*j*l^2*m^2*n*o-2*a*c*d^2*i^4*m*n^2*o-2*a^2*c*d*i^3*l*m*n^2*o-a^2*d^2*i^2*j^2*m^2*o^2+a^4*j^2*l^2*m^2*o^2-2*a^3*d*i^2*j*l*m*n*o^2-2*a^4*i*j*l^2*m*n*o^2+a^2*d^2*i^4*n^2*o^2+2*a^3*d*i^3*l*n^2*o^2+a^4*i^2*l^2*n^2*o^2)
J = I + ideal last last linears
J1 = trim mySat(J, a);
J1 = trim mySat(J1,i);
J1 = trim mySat(J1,l);
J1 = trim mySat(J1,m);
J1 = trim mySat(J1,o);
degree J1
codim J1
J2 = J1 + ideal last linears#1
time J2 = trim mySat(J2,d);
time J2 = trim mySat(J2,m);
time J2 = trim mySat(J2,n);
degree J2
codim J2
J3 = J2 + ideal last linears#0
code mySat
time J4 = trim saturate(J3, c*j+b*k);
degree J4
see J4
J' = I + ideal(linears/last);
F = product unique (linears / (x -> x#1));
F = product((factors F)/last)
time mySat(J',F);
