R = ZZ/32003[vars(0..15)]
M = genericMatrix(R,a,4,4)
I = permanents(3,M)


end

  restart
  debug needsPackage "PD"
  debug needsPackage "SingularInterface"

  load "PD/example-permanents.m2"
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
  
  
