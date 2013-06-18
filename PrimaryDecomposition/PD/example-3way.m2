-- Example: basic moves for a x b x c tables
threeWay = method()
threeWay(ZZ,ZZ,ZZ, Ring) := (a,b,c,kk) -> (
    R = kk[x_(1,1,1)..x_(a,b,c), MonomialOrder=>8];
    asets := subsets(toList(1..a), 2)/toSequence;
    bsets := subsets(toList(1..b), 2)/toSequence;
    csets := subsets(toList(1..c), 2)/toSequence;
    ideal flatten for A in asets list 
      flatten for B in bsets list
        for C in csets list (
            (a1,a2) := A;
            (b1,b2) := B;
            (c1,c2) := C;
            x_(a1,b1,c1) * x_(a1,b2,c2) * x_(a2,b1,c2) * x_(a2,b2,c1)
                - x_(a2,b1,c1) * x_(a2,b2,c2) * x_(a1,b1,c2) * x_(a1,b2,c1)
            )
    )

end

restart
  debug needsPackage "PD"
  needsPackage "UnitTestsPD"
load "PD/example-3way.m2"
I = threeWay(3,3,3,ZZ/101)

  J = ideal gens gb I;
  time C1 = splitIdeal(J, Strategy=>strat1, Verbosity=>2);
    C = splitUntil(I, Linear, 1)
    time C1 = splitUntil(C, Factorization, infinity, Verbosity=>2);
    time C2 = splitUntil(C1, DecomposeMonomials, infinity, Verbosity=>1);
    time C3 = splitUntil(C2, Linear, infinity, Verbosity=>2);
    
    time C3 = splitUntil(C1, Birational, infinity, Verbosity=>2);

time C1 = minprimes(I, Strategy=>(IndependentSet, infinity), Verbosity=>2);
I1 = saturate(I, x_(1,1,1));
I2 = I : I1;
minprimes(I, Verbosity=>2)

gbTrace=3
J1 = I : (x_(1,1,3)*x_(1,2,2)*x_(1,3,1)*x_(2,1,1)*x_(2,2,3)*x_(2,3,2)-x_(1,1,1)*x_(1,2,3)*x_(1,3,2)*x_(2,1,3)*x_(2,2,2)*x_(2,3,1));
minprimes J1

J2 = I : J1;
intersect(J1, J2) == I
degree J1
degree J2
codim J2
codim J1
J1
numgens J2
J2_44
C1 = splitUntil(J2, Factorization, 10, Verbosity=>2);
C2 = splitUntil(C1, Linear, 2);
