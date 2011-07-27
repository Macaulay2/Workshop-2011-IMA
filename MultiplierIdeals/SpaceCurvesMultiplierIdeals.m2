-- -*- coding: utf-8 -*-
----------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------
------------------------ SPACE CURVES MULTIPLIER IDEALS --------------------------------------------
----------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Copyright 2011 Claudiu Raicu, Bart Snapp, Zach Teitler
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
    	Version => "0.1", 
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

----------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------
------------------------ EXPORTS -------------------------------------------------------------------
----------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

export {
     monomialSpaceCurveMultiplierIdeal    
     }

----------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------
------------------------ PACKAGES ------------------------------------------------------------------
----------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

needsPackage "Normaliz"
needsPackage "MonomialMultiplierIdeals"


----------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------
------------------------ METHODS -------------------------------------------------------------------
----------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

-- affineMonomialCurveIdeal
--
-- Compute defining ideal of a curve in affine 3-space parametrized by monomials,
-- i.e., parametrized by t -> (t^a,t^b,t^c) for positive integers a,b,c.
--
-- Input:
--  * ring S
--  * list of integers {a,b,c}
-- Output:
--  * ideal (ideal in S defining curve parametrized by t->(t^a,t^b,t^c))
--
-- The ring S should be a polynomial ring over a field. Currently this is not checked.
-- The integers {a,b,c} should be positive. Currently this is not checked.
-- The output ideal may need to be trimmed, we do not do this.
--
-- The code for affineMonomialCurveIdeal is based on the code for
-- monomialCurveideal from Macaulay2.

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


-- ord
--
-- Compute monomial valuation of a given polynomial with respect to a vector that gives
-- the values of the variables.
--
-- Input:
--  * list mm = {a1,a2,a3,...}
--  * polynomial p
-- Output:
--  * integer
-- This computes the monomial valuation in which the variable x1 has value a1, x2 has value a2,...
-- The value of a polynomial is the MINIMUM of the values of its terms (like order of vanishing,
-- NOT like degree).
--
-- The values {a1,a2,...} should be nonnegative and there should be at least as many as the number
-- of variables appearing in the polynomial. Currently we do not check this.

ord = (mm,p) -> (
     R := ring p;
     KK := coefficientRing R;
     A := KK[gens R,Degrees=>mm];
     min flatten apply(terms p, i -> degree sub(i,A))
     );


-- sortedff
--
-- Compute the minimal generators of the defining ideal of the monomial curve parametrized
-- by t->(t^a1,t^a2,t^a3,...) and return the list of generators in order of increasing values
-- of ord({a1,a2,a3,...}, -).
--
-- Input:
--  * ring R
--  * list nn = {a1,a2,a3,...} of integers
-- Output:
--  * list of polynomials
-- The ring R should be a polynomial ring over a field. Currently this is not checked.
-- The integers {a1,a2,a3,...} should be positive. Currently this is not checked.

sortedff = (R,nn) -> (
     KK := coefficientRing R;
     genList := flatten entries gens trim affineMonomialCurveIdeal(R,nn);
     L := sort apply(genList, i -> {ord(nn,i), i});
     apply(L, i-> last i)     
     );


-- exceptionalDivisorValuation
--
-- Compute the valuation induced by the (mm,ord(mm,f_2)) exceptional divisor
-- in the resolution of singularities of the monomial curve with exponent vector nn.
--
-- Input:
--  * list of integers nn={a,b,c}
--  * list of integers mm={d,e,f}
--  * polynomial p (in 3 variables)
-- Output:
--  * integer
--
-- The valuation is defined as follows. First we computed the sorted generators (f0,f1,f2,...)
-- of the defining ideal of the curve. Writing p = f0^d * g where g is not divisible by f0,
-- the valuation of p is d*ord(mm,f1) + ord(mm,g).

exceptionalDivisorValuation = (nn,mm,p) -> (
     R := ring p;
     ff := sortedff(R,nn);
     n := 0;
     while p % ff_0 == 0 do (p = p//ff_0; n = n+1;);
     n*ord(mm,ff_1) + ord(mm,p)
     );


-- exceptionalDivisorDiscrepancy
--
-- Compute the multiplicity of the relative canonical divisor along the (mm,ord(mm,f_2)-ord(mm,f_1))
-- exceptional divisor in the resolution of singularities of a monomial curve.
--
-- Input:
--  * list of integers mm={a,b,c}
--  * sorted list of generators of the ideal of the monomial curve
-- Output:
--  * integer

exceptionalDivisorDiscrepancy = (mm,ff) -> (
     sum(mm) - 1 + ord(mm, ff_1) - ord(mm, ff_0)
     );




-- intmat2monomIdeal
--
-- Compute the monomial ideal generated by monomials given by exponent vectors taken
-- from the rows of an integer matrix. Optionally, select a subset of rows of the matrix.
--
-- Input:
--  * a matrix M with integer entries
--  * a ring R
--  * (optional) an integer d
--  * (optional) an integer c
-- Output:
--  * a monomialIdeal I
--
-- Without optional inputs:
--   For each row (a1,a2,...) of M, the monomial x1^a1*x2^a2*... is a generator of I.
-- With a single optional input d:
--   Only read rows whose last entry is equal to d.
--   Ignore the last column, i.e., (a1,a2,...,an,d) corresponds to the monomial x1^a1*...*xn^an.
-- With two optional inputs d,c:
--   Only read rows whose entry in the c'th column is equal to d. Ignore c'th column.
--
-- This code was copied from Zach Teitler's package
-- MonomialMultiplierIdeals.m2, which in turn borrows from Normaliz.m2.
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


-- monomialValuationIdeal
--
-- Compute valuation ideal {h : ord(mm,h) >= val}.
--
-- Input:
--  * ring R
--  * list of integers mm={a1,a2,...}
--  * integer val
-- Output:
--  * ideal of R.
-- The ring R should be a polynomial ring over a field.
-- The list mm should have nonnegative integers, with at least as many as the number
-- of variables in R. Currently we do not check these things.

monomialValuationIdeal = (R,mm,val) -> (
     M := (matrix{mm}|matrix{{-val}}) || id_(ZZ^(#mm+1));
     normalizOutput := normaliz(M,4);
     M2 := normalizOutput#"gen";
     intmat2monomIdeal(M2,R,1)
     );


-- exceptionalDivisorValuationIdeal
--
-- Compute valuation ideal {h : v(h) >= val}, where the valuation v is induced by the
-- (mm,ord(mm,f_2)-ord(mm,f_1)) exceptional divisor.
--
-- Input:
--  * ring R
--  * sorted list of generators of curve ideal
--  * list mm={a,b,c}
--  * integer val
-- Output:
--  * ideal

exceptionalDivisorValuationIdeal = (R,ff,mm,val) -> (
     maxpow := ceiling(val / ord(mm,ff_1));
     if maxpow < 0 then ideal(1_R) else
     sum apply(splice{0..maxpow}, i -> ideal(ff_1^i)*monomialValuationIdeal(R,mm,val-i*ord(mm,ff_1)))
     );


-- termIdeal
--
-- Compute smallest monomial ideal containing a given ideal.
--
-- Input:
--  * ideal
-- Output:
--  * monomialIdeal

termIdeal = I -> monomialIdeal flatten apply(flatten entries gens I, i -> terms i);



-- symbolicPowerCurveIdeal
--
-- Compute symbolic power of the defining ideal of a monomial space curve.
--
-- Input:
--  * ideal I
--  * integer t
-- Output:
--  * ideal
--
-- For a prime ideal I and p>=0, the symbolic power I^(p) is the ideal of functions vanishing to
-- order at least p at every point of V(I). It is the I-primary component of I^p. The non-I-primary
-- components of I^p have support contained in Sing(V(I)).
--
-- For our ideals (of monomial curves) the singular locus is a single point, the origin.
-- We compute the symbolic power by computing I^p, then saturating with respect to the ideal
-- of the origin (to remove unwanted primary components).
--
-- In the future this may be replaced by a better algorithm, perhaps?
--
-- We assume the input ideal is indeed prime, and that its unique singular point is the origin.

symbolicPowerCurveIdeal = (I,t) -> saturate(I^(max(0,floor t)));


-- intersectionIndexSet
--
-- Compute indexing set for intersection appearing in the formula for multiplier ideals.
-- This is a finite set of lattice points defined by some equations and inequalities.
-- See H.M. Thompson's paper (cited above).
--
-- Input:
--  * sorted list of generators of monomial space curve ideal
-- Output:
--  * list (of lattice points, each written as a list of integers)
--

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


-- monomialSpaceCurveMultiplierIdeal
--
-- Compute multiplier ideal of the defining ideal of a monomial space curve, ie., a curve in
-- affine 3-space parametrized by monomials, t->(t^a,t^b,t^c).
--
-- Input:
--  * ring R
--  * list of integers {a,b,c}, the exponents in the parametrization
--  * an integer or rational number t
-- Output:
--  * an ideal

monomialSpaceCurveMultiplierIdeal = method()
monomialSpaceCurveMultiplierIdeal(Ring, List, QQ) :=
monomialSpaceCurveMultiplierIdeal(Ring, List, ZZ) := (R, nn, t) -> (
     ff := sortedff(R,nn);
     curveIdeal := affineMonomialCurveIdeal(R,nn);
     
     indexList := intersectionIndexSet(ff);
     
     
     symbpow := symbolicPowerCurveIdeal(curveIdeal , t-1);
     term    := monomialMultiplierIdeal(termIdeal(curveIdeal) , t);
     
     validl  := intersect apply(indexList ,
                     mm -> exceptionalDivisorValuationIdeal(R,ff,mm,
                          floor(t*ord(mm,ff_1)-exceptionalDivisorDiscrepancy(mm,ff)) ));
     
     intersect(symbpow,term,validl)
     );


----------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------
------------------------ DOCUMENTATION -------------------------------------------------------------
----------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

beginDocumentation()

doc ///
Key
  monomialSpaceCurveMultiplierIdeal
  (monomialSpaceCurveMultiplierIdeal,Ring,List,QQ)
  (monomialSpaceCurveMultiplierIdeal,Ring,List,ZZ)
Headline
  multiplier ideal of monomial space curve
Usage
  I = monomialSpaceCurveMultiplierIdeal(R,nn,t)
Inputs
  R:Ring
  nn:List
  t:QQ
Outputs
  I:Ideal
Description
  Text
  
    Given a monomial space curve {\tt C} and a parameter {\tt t}, the function 
    {\tt monomialSpaceCurveMultiplierIdeal} computes the multiplier ideal associated to the embedding of {\tt C}
    in {\tt 3}-space and the parameter {\tt t}.
    
    More precisely, we assume that {\tt R} is a polynomial ring in three variables, {\tt n = \{a,b,c\}}
    is a sequence of positive integers of length three, and that {\tt t} is a rational number. The corresponding
    curve {\tt C} is then given by the embedding {\tt u\to(u^a,u^b,u^c)}.
  
  Example
    R = QQ[x,y,z];
    nn = {2,3,4};
    t = 5/2;
    I = monomialSpaceCurveMultiplierIdeal(R,nn,t)

///

----------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------
------------------------ TESTS ---------------------------------------------------------------------
----------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------


end

restart
debug loadPackage"SpaceCurvesMultiplierIdeals"
loadPackage "Dmodules"
R = QQ[x,y,z];
nn = {2,3,4};
I = affineMonomialCurveIdeal(R,nn)
ff = sortedff(R,nn)

intersect {
exceptionalDivisorValuationIdeal(R,ff,{1,1,2},2),
exceptionalDivisorValuationIdeal(R,ff,{1,2,2},3),
exceptionalDivisorValuationIdeal(R,ff,{2,3,4},7),
I
}
trim oo

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

t = 20/7
t = 31/14
t = 17/6
test(t)


restart
installPackage"SpaceCurvesMultiplierIdeals"
viewHelp SpaceCurvesMultiplierIdeals
