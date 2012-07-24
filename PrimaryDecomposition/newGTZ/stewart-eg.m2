-- from lecture5.m2 from Stillman's Atlanta lectures, June 2012.

restart
debug loadPackage "PrimDecomposition"

  -- make ideal
  R = QQ[e_1, e_2, e_3, e_4, g_1, g_2, g_3, g_4, r]
  I = ideal(r^2-3,e_1*g_1+e_2*g_2+e_3*g_3+e_4*g_4, (2/3)*e_1^2+(2/3)*e_3^2-(1/3)*r*e_3*g_1-g_1^2-r*e_4*g_2-g_2^2+(1/3)*r*e_1*g_3-g_3^2+r*e_2*g_4-g_4^2, (2/3)*e_1^2+(1/2)*e_2^2-(1/3)*r*e_2*e_3+(1/6)*e_3^2-(1/2)*e_2*g_1+(1/6)*r*e_3*g_1-g_1^2+(1/2)*e_1*g_2-(1/2)*r*e_4*g_2-g_2^2-(1/6)*r*e_1*g_3-(3/2)*e_4*g_3-g_3^2+(1/2)*r*e_2*g_4+(3/2)*e_3*g_4-g_4^2, (2/3)*e_1^2+(1/2)*e_2^2+(1/3)*r*e_2*e_3+(1/6)*e_3^2+(1/2)*e_2*g_1+(1/6)*r*e_3*g_1-g_1^2-(1/2)*e_1*g_2+(1/2)*r*e_4*g_2-g_2^2-(1/6)*r*e_1*g_3-(3/2)*e_4*g_3-g_3^2-(1/2)*r*e_2*g_4+(3/2)*e_3*g_4-g_4^2, (2/3)*e_1^2+(2/3)*e_3^2-(1/3)*r*e_3*g_1-g_1^2+r*e_4*g_2-g_2^2+(1/3)*r*e_1*g_3-g_3^2-r*e_2*g_4-g_4^2, (2/3)*e_1^2+(1/2)*e_2^2-(1/3)*r*e_2*e_3+(1/6)*e_3^2-(1/2)*e_2*g_1+(1/6)*r*e_3*g_1-g_1^2+(1/2)*e_1*g_2+(1/2)*r*e_4*g_2-g_2^2-(1/6)*r*e_1*g_3+(3/2)*e_4*g_3-g_3^2-(1/2)*r*e_2*g_4-(3/2)*e_3*g_4-g_4^2, (2/3)*e_1^2+(1/2)*e_2^2+(1/3)*r*e_2*e_3+(1/6)*e_3^2+(1/2)*e_2*g_1+(1/6)*r*e_3*g_1-g_1^2-(1/2)*e_1*g_2-(1/2)*r*e_4*g_2-g_2^2-(1/6)*r*e_1*g_3+(3/2)*e_4*g_3-g_3^2+(1/2)*r*e_2*g_4-(3/2)*e_3*g_4-g_4^2)
  see I
  codim I -- 6
  degree I -- 8

  equis = first splitViaIndeps I;  
  equis/codim
  equis/degree  

  leaves = flatten(equis/splitEquidimFactors)
  intersect leaves == I

  leaves = drop(leaves, 1)
  J = extendIdeal(leaves_0) -- splits at least into 2 primes (8 points over CC)
  J = ideal(J_0,J_1,J_2)

  L = ideal(J_*/numerator)
  use ring J
  J1 = sub(J, r=>r+g_2+g_3)
  L1 = ideal(J1_*/numerator)
  use ring L1
  facs = factors (eliminate(L1, {g_2,g_3}))_0
  facs = apply(facs, (mult,h) -> (mult,sub(h,r=>r-g_2-g_3)))
  
  G = facs_0_1 % L
  sub(L,R) + ideal (sub(G,R))
  extendIdeal oo
  contractToPolynomialRing oo
