-- -*- coding: utf-8 -*-
--------------------------------------------------------------------------------
-- Copyright 2007, 2011 Michael Stillman
--
-- This program is free software: you can redistribute it and/or modify it under
-- the terms of the GNU General Public License as published by the Free Software
-- Foundation, either version 3 of the License, or (at your option) any later
-- version.
--
-- This program is distributed in the hope that it will be useful, but WITHOUT
-- ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
-- FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
-- details.
--
-- You should have received a copy of the GNU General Public License along with
-- this program.  If not, see <http://www.gnu.org/licenses/>.
--------------------------------------------------------------------------------

newPackage(
	"SpaceCurvesMultiplierIdeals",
    	Version => "0.5", 
    	Date => "July 27, 2011",
    	Authors => {
	     {Name => "Zach Teitler"},
	     {Name => "Bart Snapp"},
	     {Name => "Claudiu Raicu"}
	     },
    	Headline => "multiplier ideals of monomial space curves"
    	)

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

needsPackage "Normaliz"
needsPackage "MonomialMultiplierIdeals"
--loadPackage("Normaliz", Reload=>true);
--loadPackage("MonomialMultiplierIdeals", Reload=>true);

export {
     monomialSpaceCurveMultiplierIdeal    
     }


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
     );

ord = (mm,p) -> (
     R := ring p;
     KK := coefficientRing R;
     A := KK[gens R,Degrees=>mm];
     min flatten apply(terms p, i -> degree sub(i,A))
     );


sortedff = (R,nn) -> (
     KK := coefficientRing R;
     L := sort apply(flatten entries gens affineMonomialCurveIdeal(R,nn), i -> {ord(nn,i), i});
     apply(L, i-> last i)     
     );


exceptionalDivisorValuation = (nn,mm,p) -> (
     R := ring p;
     ff := sortedff(R,nn);
     n := 0;
     while p % ff_0 == 0 do (p = p//ff_0; n = n+1;);
     n*ord(mm,ff_1) + ord(mm,p)
     );

km = (mm,ff) -> sum(mm) - 1 + ord(mm, ff_1) - ord(mm, ff_0);




--
-- The code below was copied directy from Zach Teitler's Pacakage
-- MonomialMultiplierIdeas.m2
-- 

intmat2monomIdeal = method();
intmat2monomIdeal ( Matrix, Ring ) := (M,R) -> (
  if ( numColumns M > numgens R ) then (
    error("intmat2monomIdeal: Not enough generators in ring.");
  );
  
  genList := apply( 0..< numRows M ,
                    i -> R_(flatten entries M^{i}) );
  
  return monomialIdeal genList;
);
-- only include rows whose last entry is d; and ignore last column
intmat2monomIdeal ( Matrix, Ring, ZZ ) := (M,R,d) -> intmat2monomIdeal(M,R,d,numColumns(M)-1);
-- only include rows with entry 'd' in column 'c'; and ignore column 'c'
intmat2monomIdeal ( Matrix, Ring, ZZ, ZZ ) := (M,R,d,c) -> (
  if ( numColumns M > 1 + numgens R ) then (
    error("intmat2monomIdeal: Not enough generators in ring.");
  );
  
  rowList := select( 0 ..< numRows M , i -> (M_(i,c) == d) ) ;
  columnList := delete( c , toList(0 ..< numColumns M) );
  
  M1 := submatrix(M,rowList,columnList);
  
  return intmat2monomIdeal(M1,R);
);

--
-- The code above was copied directy from Zach Teitler's Pacakage
-- MonomialMultiplierIdeas.m2
-- 

monomialValuationIdeal = (R,mm,val) -> (
     M := (matrix{mm}|matrix{{-val}}) || id_(ZZ^(#mm+1));
     normalizOutput := normaliz(M,4);
     M2 := normalizOutput#"gen";
     intmat2monomIdeal(M2,R,1)
     );


exceptionalDivisorValuationIdeal = (R,ff,mm,val) -> (
     maxpow := ceiling(val / ord(mm,ff_1));
     if maxpow < 0 then ideal(1_R) else
     sum apply(splice{0..maxpow}, i -> ideal(ff_1^(maxpow-i))*monomialValuationIdeal(R,mm,i))
     );

termIdeal = I -> monomialIdeal flatten apply(flatten entries gens I, i -> terms i);

-- here we wish to compute the symbolic power I^(floor t). We'll use
-- the saturate command, but in the future there may be a better
-- option.

symbolicPowerCurveIdeal = (I,t) -> saturate(I^(max(0,floor t)));


intersectionIndexSet = (ff) -> (
     uu := {(exponents(ff_0))_0, (exponents(ff_1))_0};
     vv := {(exponents(ff_0))_1, (exponents(ff_1))_1};
     
     cols := #(uu_0);
     candidateGens1 := (normaliz(matrix{uu_0 - vv_0} || matrix{vv_0 - uu_0} || matrix{uu_1 - vv_1} || id_(ZZ^cols),4))#"gen";
     candidateGens2 := (normaliz(matrix{uu_0 - vv_0} || matrix{vv_0 - uu_0} || matrix{vv_1 - uu_1} || id_(ZZ^cols),4))#"gen";
     candidateGens  := candidateGens1 || candidateGens2;
     rhoEquation    := (transpose matrix {uu_1-uu_0}) | (transpose matrix {vv_1-vv_0});
     
     T := candidateGens * rhoEquation;
     rows := toList select(0..<numRows T, i -> all(0..<numColumns T, j -> T_(i,j) > 0));
     unique apply(rows, i -> flatten entries candidateGens^{i})
     );


monomialSpaceCurveMultiplierIdeal = (R, nn, t) -> (
     ff := sortedff(R,nn);
     curveIdeal := affineMonomialCurveIdeal(R,nn);
     
     indexList := intersectionIndexSet(ff);
     
     
     symbpow := symbolicPowerCurveIdeal(curveIdeal , t-1);
     term    := monomialMultiplierIdeal(termIdeal(curveIdeal) , t);
     
     validl  := intersect apply(indexList , mm -> exceptionalDivisorValuationIdeal(R,ff,mm,floor(t*ord(mm,ff_1)-km(mm,ff))));
     
     intersect(symbpow,term,validl)
     );

-- intersect(Ideal,Ideal,Ideal) etc



end

restart
--load "bart.m2"
debug loadPackage"SpaceCurvesMultiplierIdeals"
loadPackage "Dmodules"
R = QQ[x,y,z];
nn = {2,3,4};
I = affineMonomialCurveIdeal(R,nn)
ff = sortedff(R,nn)
time A = monomialSpaceCurveMultiplierIdeal(R,nn,20/7)
time B = multiplierIdeal(I,20/7)
trim A
trim B

test = (t) -> (
     A := monomialSpaceCurveMultiplierIdeal(R,nn,t);
     B := multiplierIdeal(I,t);
     if ( A == B ) then (
          print "ok";
     ) else (
          print "no";
     );
     );

t = 5/2
test(t)
     