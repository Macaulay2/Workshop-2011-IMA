restart
installPackage "MonomialMultiplierIdeals"
viewHelp MonomialMultiplierIdeals

R = QQ[x,y];
I = monomialIdeal(y^2,x^3);
monomialMultiplierIdeal(I,5/6)

-- End functionality:
-- input: sequence of integers and a real number
-- output: multiplier ideal

-- Intermediate functionality (we need):
-- Symbolic power of I
-- term ideal of the monomial ideal
-- some intersection of the lattice points. 

KK = ZZ/101
R = KK[x,y,z,w]	    
affineMonomialCurveIdeal = (S, a) -> (
          -- check that S is a polynomial ring over a field
          n := # a;
          if not all(a, i -> instance(i,ZZ) and i >= 1)
            then error "expected positive integers";
	  t := symbol t;
          k := coefficientRing S;
          M1 := monoid [t];
          M2 := monoid [Variables=>n];
          R1 := k M1;
          R2 := k M2;
          t = R1_0;
          mm := matrix table(1, n, (j,i) -> t^(a#i));
          j := generators kernel map(R1, R2, mm);
          ideal substitute(j, submatrix(vars S, {0..n-1}))
          )
     

-- term ideal is just the ideal of the terms of the gens... right?
termIdeal = I -> monomialIdeal flatten apply(flatten entries gens I, i -> terms i);

monomialMultiplierIdeal(termIdeal I,5/6)

code methods leadTerm
