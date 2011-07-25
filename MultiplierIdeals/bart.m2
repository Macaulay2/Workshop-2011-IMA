restart
installPackage "MonomialMultiplierIdeals"
viewHelp MonomialMultiplierIdeals

R = QQ[x,y];
I = monomialIdeal(y^2,x^3);
monomialMultiplierIdeal(I,5/6)

-- End functionality:
-- input: ring, sequence of integers, and a real number
-- output: multiplier ideal

-- Intermediate functionality (we need):
-- Symbolic power of I.
-- term ideal of the monomial ideal. DONE!
-- some intersection of the lattice points. 

-- This implementation is based on the algorithm given in
-- H.M. Thompson's paper: "Multiplier Ideals of Monomial Space
-- Curves."


KK = ZZ/101
R = KK[x,y,z,w]	    

-- the code for affineMonomialCurveIdeal is based off of the code for
-- monomialCurveideal

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
     

I = affineMonomialCurveIdeal(R,{2,3,4})

-- term ideal is just the ideal of the terms of the gens... right?

termIdeal = I -> monomialIdeal flatten apply(flatten entries gens I, i -> terms i);

termIdeal I




-- here we wish to compute the symbolic power I^(floor t). We'll use
-- the saturate command, but in the future there may be a better
-- option.

symbolicPowerCurveIdeal = (I,t) -> saturate(I^(floor t));



-- now we attack the last part of the intersection, with the
-- "valuations" and the "G"

describe R

ord(m,x)

ord = (R,mm) -> substitute(gens R, apply(#mm-1, i -> gens R_i => mm_i));
ord(R,{1,2,3,4}) x

gens R
nu = map(QQ, 
     
     