-- Input  : A (polynomial) ring
-- Output : A pair of endomorphisms of the ring.  Say R = kk[x_1,...,x_n].  Then
--          each map sends x_i to x_i for i < n, but the first map sends
--          x_n ---> x_n + (random linear form in x_1,...,x_{n-1}).  The inverse
--          of course sends x_n ---> x_n - (random linear form above).
--          The map also fixes those elements of us, and the coordinate change does not involve the elements of us
--          us = baseVars
getCoordChange = method()
getCoordChange(Ring,List) := (R,us) ->
(
   randTerms := terms random(1,R);
   okVars := reverse sort toList(set gens R - set us);
   lastVar := last okVars;
   myTerms := select(randTerms, i -> isSubset(support i, okVars) and support i != {lastVar});
   coordChange := map(R, R, {lastVar => lastVar + sum myTerms});
   coordChangeInverse := map(R,R,{lastVar => lastVar - sum myTerms});
   (coordChange,coordChangeInverse,lastVar)
)
TEST ///
restart
load "newGTZ.m2"
debug newGTZ
R = ZZ/32003[a,b,c,x]
(phi,phiInverse,lastVar) = getCoordChange(R,{x})
phi*phiInverse
phiInverse*phi
///

-- Input  : An ideal I, and a list of variables myVars.  The list myVars is supposed to be
--          the set of variables that were inverted because they were an independent set
--          earlier in the algorithm (and hence of the input)
-- Output : 
contractBack = method()
contractBack(Ring,Ideal) := (R,I) ->
(
   fracR := frac R;
   gensI := flatten entries gens I;
   myMapFracR := map(fracR, ring I);
   myMapR := map(R, ring I);
   numerators := apply(gensI, i -> numerator myMapFracR(i));
   newI := ideal numerators;
   myVars := (flatten entries vars coefficientRing ring I) / myMapR;
   sepAndSat(newI,myVars)
)

sepAndSat = method()
sepAndSat(Ideal,List) := (I,myVars) ->
(
   mySep := first getSeparator(I, myVars);
   trim saturate(I,mySep)
)

-- Input  : 
-- Output : 
invertVariables = method(Options => {MonomialOrder => null})
invertVariables(List,List,Ring) := opts -> (baseVars, fiberVars, R) ->
(
   local newR;
   if (baseVars == {}) then
   (
      if (opts.MonomialOrder === null)
         then newR = R
         else newR = newRing(R, MonomialOrder => opts.MonomialOrder);
   )
   else
   (
      if (opts.MonomialOrder === null)
         then newR = frac((coefficientRing R)[baseVars])[fiberVars]
         else newR = frac((coefficientRing R)[baseVars])[fiberVars,MonomialOrder => opts.MonomialOrder];
   );
   mapRtoNewR := map(newR,R);
   mapRtoNewR
)

-- Input  : I, a zero dimensional ideal in kk[x_1,...,x_n] (note that kk could have variables too)
-- Output : The 'minimal polynomial' of x_n modulo I.
getMinimalPolynomial = method()
getMinimalPolynomial(Ideal) := (I) ->
(
   -- both these lines, and the lines following are the hold up in computations (usually)
   --newR = newRing(ring I, MonomialOrder => Lex)
   --gbI := first entries gens gb I;
   --f := first select(gbI, i -> support(i) == {last gens ring I});
   elimI := trim eliminate(I, take(gens ring I,(#gens ring I)-1));
   first flatten entries gens elimI
)

-- Input  : 
--          
-- Output : 
-- This is a non-fraction field version of the getMinimalPolynomial
getMinimalPolynomial2 = method()
getMinimalPolynomial2(Ideal,List,RingElement,RingElement) := (I,us,x,y) ->
(
   J := substitute(I,{x => y});
   elimVars := toList(set gens ring I - set us - set {x});
   -- time this thing!
   elimJ := eliminate(J, elimVars);
   --error "debug";
   --if (numgens elimJ == 0 and isSubset(ideal elimVars,J)) then y
   if numgens elimJ != 1 then error "Could not find minimal polynomial."
   else elimJ_0
)

TEST ///
restart
load "newGTZ.m2"
debug newGTZ
R = ZZ/32003[a,b,c,d,e,h]
I = ideal(
         a+b+c+d+e,
	 d*e+c*d+b*c+a*e+a*b,
	 c*d*e+b*c*d+a*d*e+a*b*e+a*b*c,
	 b*c*d*e+a*c*d*e+a*b*d*e+a*b*c*e+a*b*c*d,
	 a*b*c*d*e-h^5)
independentSets I
mySep = first getSeparator(I,{c})
Isat = saturate(I,mySep)
getMinimalPolynomial2(Isat,{c},d,d)
phi = (getCoordChange(R))_0
getMinimalPolynomial2(Isat,{c},h,phi(h))
///

-- Input  :
-- Output :
invertLinearRingMap = method()
invertLinearRingMap(RingMap) := (f) ->
(
   R := target f;
   map(R,R,(vars R)*(jacobian f.matrix)^(-1))
)
TEST ///
restart
load "newGTZ.m2"
debug newGTZ
R = ZZ/32003[a,b,c]
f = map(R,R,{c => c+a+b})
g = invertLinearRingMap(f)
f*g
g*f
///

-- Input  : An ideal I that is zero dimensional over k(us)[xs\us] and saturated with respect to us.  The change of coordinates x => y is used.
-- Output : A list of ideals of the form (I,phiInverse(h_i)) where the h_i are powers of irred polys
--          such that prod {h_i} is the minimal polynomial of y over I after a change of coords in last variable
splitZeroDimensionalIdeal = method()
splitZeroDimensionalIdeal(Ideal,List,RingElement,RingElement) := (I, us, x, y) ->
(
   mySep := first getSeparator(I,us);
   Isat := saturate(I,mySep);
   myMap := map(ring I, ring I, {x => y});
   -- using this since myMap^(-1) is not implemented yet
   myMapInverse := invertLinearRingMap(myMap);
   factorList := apply(toList factor getMinimalPolynomial2(Isat, us, x, y), toList);
   factorList = select(factorList, fac -> first degree fac#0 > 0);
   << "Factor List:" << endl;
   << netList factorList << endl;
   idealList := apply(factorList, fac -> ideal (myMapInverse fac#0)^(fac#1) + I);
   idealList = apply(idealList, J -> time sepAndSat(J,us));
   --error "debug";
   apply(idealList, J -> trim ideal gens gb J)
)
splitZeroDimensionalIdeal(Ideal,List) := (I,us) ->
(
   (phi,phiInverse,lastVar) := getCoordChange(ring I,us);
   splitZeroDimensionalIdeal(I, us, lastVar, phi(lastVar))
)
TEST ///
restart
load "newGTZ.m2"
debug newGTZ
R = ZZ/32003[a,b,c,d,e,h]
I = ideal(
         a+b+c+d+e,
	 d*e+c*d+b*c+a*e+a*b,
	 c*d*e+b*c*d+a*d*e+a*b*e+a*b*c,
	 b*c*d*e+a*c*d*e+a*b*d*e+a*b*c*e+a*b*c*d,
	 a*b*c*d*e-h^5)
independentSets I
mySep = first getSeparator(I,{c})
Isat = saturate(I,mySep)
time splitZeroDimensionalIdeal(Isat,{c},h,a+7*b+13*d+5*e+9*h)
///

-- Input  : A list xs, and a function f on the elements of xs.  The return value of f should be a tuple,
--          the first coordinate of which is a boolean.
-- Output : The result of apply(xs,f) until a BooleanValue (in options) is achieved as output from f
applyUntil = method(Options => {BooleanValue => false})
applyUntil(List, Function) := opts -> (xs, f) ->
(
   retVal := for i from 0 to #xs-1 list
             (
	        temp := f(xs#i);
		if (temp == opts.BooleanValue) then i = #xs;
		temp
             );
   retVal
)

-- Input  : A zero dimensional ideal I, and a resultSoFar.
-- Output : 
primDecZeroDimField = method(Options => {Verbosity => 0})
primDecZeroDimField(Ideal, List, Ideal) := opts -> (I, variables, resultSoFar) ->
(
   splitTime := timing (compList := splitZeroDimensionalIdeal(I, variables));

   if (opts.Verbosity > 0) then << "Splitting time : " << splitTime#0 << endl;

   -- problem: compList's ideals are not in general position at this point.  I think
   -- one needs to leave them with coords changed, and then change them back.
   genPosList := applyUntil(compList, J -> isPrimaryZeroDim(J));
   if (genPosList != {}) then
   (
      isInGenPos := all (genPosList, i -> i);
      if (not isInGenPos) then (
	 error "Uhoh.";
         -- try again?
	 compList = primDecZeroDimField(I, variables, resultSoFar, opts);
      );
   )
   else compList = {};
   compList
)

-- Input  : A RingElement g in a polynomial ring of the form frac(kk[baseVars])[fiberVars].
-- Output : A factorization of the numerator of g.  WARNING: Units in frac(kk[baseVars]) are not returned as factors.
newFactor = method()
newFactor(RingElement) := (g) -> (
   -- g is in a polynomial ring of the form frac(kk[baseVars])[fiberVars].
   -- this function is an attempt to factor the numerator of g.
   fiberVars := gens ring g;
   baseVars := gens coefficientRing ring g;
   newF := frac(ultimate(coefficientRing, ring g)[baseVars | fiberVars]);
   h := substitute(g, newF);
   factorList := apply(toList factor numerator h, toSequence);
   factorList = apply(factorList, (irr,pow) -> (substitute(irr,ring g),pow));
   select(factorList, (irr,pow) -> not isSubset(set support irr, set baseVars))
)


TEST ///
restart
load "newGTZ.m2"
debug newGTZ
R = ZZ/32003[a,b,c,d,e,f,g,h,i, MonomialOrder=>Lex]
I = ideal(i,h,g,e+d,c,b*d+a*e)
I = ideal gens gb I
support first independentSets I
isPrimaryZeroDim(I)
///

TEST ///
restart
load "newGTZ.m2"
debug newGTZ
R = QQ[a,b,c,d,e,h]
idealList = {ideal(e-h,d-h,c-h,a+b+3*h,b^2+3*b*h+h^2),ideal(e-h,c+d+3*h,b-h,a-h,d^2+3*d*h+h^2),ideal(e-h,d-h,b+c+3*h,a-h,c^2+3*c*h+h^2),ideal(e-h,a+b+c+d+h,d^2-c*h,c*d-b*h,b*d+b*h+c*h+d*h+h^2,c^2+b*h+c*h+d*h+h^2,b*c-h^2,b^2-d*h)}
isPrimaryZeroDim first idealList
idealList / (I -> time isPrimaryZeroDim I)

restart
load "newGTZ.m2"
debug newGTZ
R = ZZ/32003[a,b,c,d,h]
I = ideal(c-d,a+b+2*d,d^2+h^2,b^2+2*b*d-h^2)
isPrimaryZeroDim I

restart
loadPackage "newGTZ"
debug newGTZ
R = ZZ/32003[a,b,c,d,e,f,g,h,j,k,l, MonomialOrder=>Lex]
--R = ZZ/32003[a,b,c,d,e,f,g,h,j,k,l]
--R = ZZ/32003[reverse{a,b,c,d,e,f,g,h,j,k,l}]
I = ideal(h*j*l-2*e*g+16001*c*j+16001*a*l,h*j*k-2*e*f+16001*b*j+16001*a*k,h*j^2+2*e^2+16001*a*j,d*j^2+2*a*e,g*h*j+e*h*l+8001*d*j*l+16001*c*e+16001*a*g,f*h*j+e*h*k+8001*d*j*k+16001*b*e+16001*a*f
          ,e*g*j+8001*c*j^2+e^2*l,d*g*j+d*e*l+16001*a*c,e*f*j+8001*b*j^2+e^2*k,d*f*j+d*e*k+16001*a*b,d*e*j-a*h*j-16001*a^2,d*e^2-a*e*h-8001*a*d*j,d*g*k*l-c*h*k*l-d*f*l^2+b*h*l^2-2*c*f*g+2*b*g^2-16001
       	  *c^2*k+16001*b*c*l,d*g*k^2-c*h*k^2-d*f*k*l+b*h*k*l-2*c*f^2+2*b*f*g-16001*b*c*k+16001*b^2*l,d*g^2*k-c*g*h*k-d*f*g*l+c*f*h*l-8001*c*d*k*l+8001*b*d*l^2+16001*c^2*f-16001*b*c*g,d*f*g*k-b*g*h*k-
       	  8001*c*d*k^2-d*f^2*l+b*f*h*l+8001*b*d*k*l+16001*b*c*f-16001*b^2*g,c*f*g*k-b*g^2*k-8001*c^2*k^2-c*f^2*l+b*f*g*l-16001*b*c*k*l-8001*b^2*l^2,e^2*g*k+8001*c*e*j*k-e^2*f*l-8001*b*e*j*l,d*g*h*l^2
       	  -c*h^2*l^2-8001*d^2*l^3+2*d*g^3-2*c*g^2*h+16000*c*d*g*l+c^2*h*l-8001*c^3,d*f*h*l^2-b*h^2*l^2-8001*d^2*k*l^2+2*d*f*g^2-2*b*g^2*h+16001*c*d*g*k+16001*c*d*f*l+16001*b*d*g*l+b*c*h*l-8001*b*c^2,
       	  d*f*h*k*l-b*h^2*k*l-8001*d^2*k^2*l+2*d*f^2*g-2*b*f*g*h+16001*c*d*f*k+16001*b*d*g*k-16001*b*c*h*k+16001*b*d*f*l-16001*b^2*h*l-8001*b^2*c,d*f*h*k^2-b*h^2*k^2-8001*d^2*k^3+2*d*f^3-2*b*f^2*h+
       	  16000*b*d*f*k+b^2*h*k-8001*b^3)
--I = ideal gens gb I
--describe ring I
isPrimaryZeroDim(I)

restart
load "newGTZ.m2"
debug newGTZ
R = QQ[a,b,c,d]
I = ideal apply(1 .. 4, i -> random(3,R))
time(isPrimaryZeroDim I)
ourPD3 = newPD(I,Verbosity=>2,Strategy=>{GeneralPosition});
///

-- Input : Lex GB of an ideal of k(independentVars)[fiberVars]
-- Output: Constructs the g_i from proposition 5.5 in GTZ.
getVariablePowerGenerators=method()
getVariablePowerGenerators(List,List) := (G,fiberVars) -> (
   independentVars := toList (set gens ring first G) - set fiberVars;
   apply(#fiberVars, i -> first select( G, g -> isSubset(set support leadTerm g, set ({fiberVars#i} | independentVars))))
)

-- This function should be called only on ideals before a change of coordinates have been applied.
isPrimaryZeroDim = method()
isPrimaryZeroDim(Ideal) := (I) ->
(
   R := ring I;
   independentVars := support first independentSets I;
   fiberVars := reverse sort toList (set gens R - set independentVars);
   
   -- order according to fiberVars | independentVars
   -- compute a basis in GRevLex with nicely sorted variables will speed up computing lex order later
   ROrdered  := (coefficientRing R)[ independentVars | fiberVars]; 
   psiOrdered := map(ROrdered, R);
   I = gens gb psiOrdered I;
   (phi,phiInverse,lastVar) := getCoordChange(ring I,independentVars); 
   
   RLex := (coefficientRing R)[fiberVars | independentVars, MonomialOrder => {Lex=>#fiberVars,GRevLex=>#independentVars}];
   
   -- try using the fraction field here?
   
   J := phi I;
   psi := map(RLex,ROrdered);
   J = psi(J);
   fiberVars = fiberVars / psiOrdered;
   fiberVars = fiberVars / psi;
   
   G := flatten entries gens gb J;
   gs := getVariablePowerGenerators(G,fiberVars);
   -- note: last gs need not be a power of a linear form! (note that prop 7.3 has no condition on g_n)
   getLinearPowers(G,gs,fiberVars)
)

-- Pass in a lex GB of an ideal I, a set of gs as in prop 5.5 for I, and a list of variables forming the complement of an independent set for I
-- Should return the linear powers that appear in GTZ Prop 7.3 (or DGP algorithm 8, pg 11)
getLinearPowers = method()
getLinearPowers(List,List,List) := (G, gs, fiberVars) ->
(
  R := ring first G;
  kk := coefficientRing R;
  independentVars := sort toList (set gens R - set fiberVars);
  --S := R/radical ideal last gs;
  Q := frac (kk[independentVars])[fiberVars];
  --error "err";
  S := Q/sub(radical ideal last gs, Q);
  --S := Q/sub(ideal last gs, Q);
  -- need to pass to the fraction field first, since the polynomial may not be monic yet.
  linearFactorList := apply(reverse toList (0..(#fiberVars - 2)), i -> (   gi := first (trim ideal substitute(gs#i,S))_*;
									   fiberVars = apply(fiberVars, x -> substitute(x,S));
									   xi := fiberVars#i;
	    	      	   	     	       	    	      	   	   deggi := degree(xi,gi);
									   --error "err";
	                                                                   gi = gi // coefficient(xi^deggi,gi);
									   -- store the coefficients
									   (mons,coeffs) := coefficients gi;
									   -- get the indices of monomials containing xi^(deggi-1)
									   monomialIndices := select(#(flatten entries mons), i -> degree(xi,(flatten entries mons)#i) == deggi-1);
									   -- reconstruct coeff of xi^(deggi-1) from the indices
									   degGiMinusOneCoeff := (sum apply(monomialIndices, i -> (flatten entries mons)#i*(flatten entries coeffs)#i)) // xi^(deggi-1);
									   testHi := (xi + deggi^(-1)*degGiMinusOneCoeff);
									   if (testHi^(deggi) != gi) then error "Not a linear power!";
									   newI := ideal S + sub(testHi,Q);
									   S = Q/newI;
									   print testHi;
									   testHi));
  linearFactorList = reverse linearFactorList;
  -- if we make it through the apply without an error, then all the factors are linear.
  -- we should return the linear factor list.  However, before doing this, we need to clear denominators and put the linear forms
  -- back in the polynomial ring.
  return true;
)

irredPower = method()
irredPower(RingElement) := (f) ->
(
   factorList := apply(toList factor f, toList);
   max(factorList / first / degree / first)
)

