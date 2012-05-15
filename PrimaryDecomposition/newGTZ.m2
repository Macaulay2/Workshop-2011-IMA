-- THIS IS BEING DEVELOPED NOW!! --
-- This is not meant for general use yet.

newPackage(
	"newGTZ",
    	Version => "0.5", 
    	Date => "June 25, 2009",
    	Authors => {{Name => "Frank Moore", 
		  Email => "frankmoore@math.cornell.edu", 
		  HomePage => "http://www.math.cornell.edu/~frankmoore/"},
	            {Name => "Mike Stillman",
		  Email => "mike@math.cornell.edu", 
		  HomePage => "http://www.math.cornell.edu/~mike/"},
	            {Name => "Ben Lundell",
		  Email => "blundell@math.cornell.edu", 
		  HomePage => "http://www.math.cornell.edu/People/Grads/lundell.html"},
	            {Name => "Jen Biermann",
		  Email => "jbiermann@math.cornell.edu", 
		  HomePage => "http://www.math.cornell.edu/People/Grads/biermann.html"}},
    	Headline => "A (new) Primary Decomposition Package following loosely the GTZ algorithm",
    	DebuggingMode => true
    	)

export {
     getSaturation,
     newPD,
     GeneralPosition,
     BasicPD,
     getSeparator,
     isIrredundantPD,
     isEqualPDs,
     testPD
     }

needs (newGTZ#"source directory"|"newGTZ/newGTZGenPos.m2")
--needs "./newGTZGenPos.m2"

-- The following variables are used to keep track of times during computation
eliminationTime = 0.0
sepAndSatTime = 0.0
sepAndSatPPDTime = 0.0
factorTime = 0.0
primaryTime = 0.0
splitZeroCleanupTime = 0.0
intersectionTime = 0.0

-- Comments:
-- bug in "help RingElement"
-- radical does not work for ideals over ZZ with nonunit coefficients
-- cannot factor polynomials with coefficients not in QQ or ZZ/p


getPCoeff = method()
getPCoeff(RingElement, RingElement) := (g,p) ->
(
   --- returns the pair (n,g/p^n) where p^n is the largest power of p dividing g,
   if (p == 0_(ring g)) then (0_(ring g),g)
   else
   (
      pPower := p;
      f := g % pPower;
      n := 1;
      while (f == 0) do
      {
         n = n+1;
	 pPower = p*pPower;
         f = g % pPower;
      };
      (n-1, g // (pPower // p))
   )
)
TEST ///
  restart
  load "newGTZ.m2"
  debug newGTZ
  R = ZZ[x,y]
  f = 125*x*y+25*x^2
  assert(getPCoeff(f,5_R) == (2,x^2+5*x*y))
/// 

--- also return a smarter element for saturation?
getSaturation = method()
getSaturation(Ideal, RingElement) := (I,s) ->
(
   -- This function takes an ideal and a ring element s as input, and
   -- computes the saturation of I with respect to s, as well as the integer n
   -- such that (I:s^\infty) = (I:s^n) [which exists by Noetherianness]
   satI := saturate(I,s);
   -- add *option* to iteravely compute colons later?
   n := 0;
   J := compress((gens satI) % I);
   while J != 0 do (
      J = compress((s**J) % I);
      n = n+1;
   );
   (satI,n)
)

TEST ///
  restart
  load "newGTZ.m2"
  R = ZZ/32003[a..d]
  I = (ideal vars R)^3
  assert (getSaturation(I,a) == (ideal 1_R,3))
  assert (getSaturation(I,a*b) == (ideal 1_R,2))
  J = (ideal (a,b,c-d))*I
  assert (getSaturation(J,a) == (ideal 1_R, 4))
  assert (getSaturation(J,d) == (ideal (c - d, b, a), 3))
///

---------------------------------------
-- Lead terms under a product order ---
---------------------------------------
getProductOrderLeadTerms = method()
getProductOrderLeadTerms(Ideal, List) := (I, baseVars) ->
(
   -- This function takes an ideal I and a list of variables baseVars as input
   -- and returns a pair of matrices (mons, cs) where mons are the monomials in the ideal
   -- of lead terms of a gb of I, and cs are the coefficients, but with respect to
   -- a product order kk[fiberVars][baseVars].  See example below for behavior
   R := ring I;
   allVars := set gens R;
   fiberVars := toList(allVars - set baseVars);
   RU := (coefficientRing R) monoid([fiberVars,baseVars,
	     MonomialOrder=>{#fiberVars,#baseVars}]);
   J := substitute(I,RU);
   leadTermsJ := leadTerm(1, gens gb J);
   (mons,cs) := coefficients(leadTermsJ, Variables => toList(0..#fiberVars-1));
   mons = substitute(mons, R);
   cs = substitute(cs, R);
   (mons, cs)
)

getProductOrderHashTable = method()
getProductOrderHashTable(Ideal, List) := (I, baseVars) -> (
   -- This function takes an ideal and a list of variables as input.  The
   -- list of variables forms part of an independent set for the ideal I.
   -- Its output is just a HashTable version of the data output in the
   -- getProductOrderLeadTerms function.
   (mons,cs) := getProductOrderLeadTerms(I, baseVars);
   monsList := flatten entries mons;
   monHash := hashTable for i from 0 to #monsList-1 list (
	monsList#i => flatten entries compress cs^{i});
   monHash
)

factorPHashTable = method()
factorPHashTable(HashTable,RingElement) := (monHash,p) ->
(
   --- monHash is a hash table of the form (monomial, list of polynomials) and p is a prime number or zero.
   --- The function moves the powers of p from the values to the keys of the HashTable monHash
   --- the output of this function has key, value pairs of the form (monomial, ideal).  Therefore, in the p = 0
   --- case we need only convert the value to the ideal it generates.
   if (p =!= 0_(ring p)) then (hashTable apply(pairs monHash, (m, val) -> (
	       pParts := apply(val, i -> getPCoeff(i,p));
	       minPPower := min (pParts / first);
	       newGs := select(pParts, (pow, g) -> pow === minPPower);
	       (p^minPPower*m, trim ideal (newGs / (x -> x#1))))))
   else (hashTable apply(pairs monHash, (m, val) -> (m, trim ideal val)))
)

minimalizeHashTable = method()
minimalizeHashTable(HashTable) := (monHash) ->
(
   --- the input has key, value pairs of the form (Monomial, ideal)
   --- use monomialIdeal instead of ideal for field coefficientRings?
   local minGens;
   kk := coefficientRing ring first keys monHash;
   minGens = if (isField kk) then 
     set flatten entries gens monomialIdeal keys monHash 
   else 
     set flatten entries mingens ideal keys monHash;
   --if (p =!= 0_(ring p)) then 
   --     minGens = set flatten entries mingens ideal keys monHash 
   --else minGens = set flatten entries gens monomialIdeal keys monHash;
   hashTable select(pairs monHash, (m,val) -> member(m,minGens))
)

TEST ///
  restart
  load "newGTZ.m2"
  debug newGTZ
  R = ZZ/32003[x,y,z]
  I = ideal (y^2*z-15*x*z^2,5*x^2*y^3-25*x*y*z^3)
  independentSets(I)
  getProductOrderLeadTerms(I,{x})
  H = getProductOrderHashTable(I,{x})
  factorPHashTable(H, 0_R)  -- do we need this one??
///

getSeparatorZZ = method()
getSeparatorZZ(Ideal, List, RingElement) := (I, baseVars, p) ->
(
   --- This function takes as input an ideal, a prime number p, and a list of variables so that
   --- p, together with the list of variables are an independent set for I after localizing at p.
   --- It returns a pair (s, monHash) where monHash is the internally used hashTable to construct
   --- s, and s is an element so that I = (I:s^\infty) \cap (I,s) [a separator].  This is the
   --- crucial decomposition in the GTZ algorithm.
   --- Step 1:  Make the hash table that contains the monomials and coeffs in the grobner basis of I
   ---          with respect to the product order given by the variables input
   monHash := getProductOrderHashTable(I,baseVars);
   --- Step 2:  If necessary, move the powers of p from the values to the keys of the table, since
   ---          coefficients does not do this work for us
   monHash = factorPHashTable(monHash,p);
   --- Step 3:  Attempt to be a little clever coming up with a small separator by only using those values corresponding to minimal
   ---          generators of the ideal generated by the keys
   monHash = minimalizeHashTable(monHash);
   --- Step 4:  The s we desire is now the intersection (of the radicals of, but we can't do radical over ZZ) of the values in the HashTable we have built
   --- s := ((values monHash) / radical // intersect)_0;
   s := ((values monHash) // intersect)_0;
   (s, monHash)
)

getSeparator = method()
getSeparator(Ideal, List) := (I, baseVars) ->
(
   p := 0_(ring I);
   monHash := getProductOrderHashTable(I,baseVars);
   monHash = factorPHashTable(monHash,p);
   monHash = minimalizeHashTable(monHash);
   s := ((values monHash) / (i -> ideal gens radical i) // intersect)_0;
   (s, monHash)
)

TEST ///
  restart
  load "newGTZ.m2"
  debug newGTZ
  loadPackage "ExampleIdeals"
  R = ZZ[vars(0..8)];
  I = permanents(2, genericMatrix(R,3,3))
  getSeparatorZZ(I,{a,b,c},2_(ring I))
  R' = QQ[vars(0..8)];
  use R'
  I' = substitute(I,R');
  getSeparator(I',{a,b,c})
  newPD(I',Verbosity => 2)
///

debug PrimaryDecomposition
-- uses findNonMember and removeScalarMultipleColumns, both of which call engine functions.
-- so must just import the PrimaryDecomposition package symbols with debug to use them
-- so I don't have to import the core symbols
getComponentSep = method()
getComponentSep(List,ZZ) := (compList,i) -> (
   R := ring first compList;
   ss := apply(toList(0..#compList-1), j -> if i == j then 0_R else findNonMember(compList#j, compList#i));
   -- the following throws out zeros, and elements which are                                                                                                                                                                   
   -- not constant multiples of others.                                                                                                                                                                                        
   seps := flatten entries removeScalarMultipleColumns matrix {ss};
   -- be even more clever here?
   product seps
)

debug PrimaryDecomposition
primDecZeroDim = method(Options => {Verbosity => 0, Strategy=> {}})
primDecZeroDim(Ideal, List, Ideal) := opts -> (I, independentVars, resultSoFar) ->
(
   pdList :=
     if member(BasicPD,set opts.Strategy) then 
             primaryDecomposition I
          else if member(GeneralPosition, set opts.Strategy) then 
	     primDecZeroDimField(I,independentVars,resultSoFar,Verbosity => opts.Verbosity)
	  else 
             (
                compList := decompose I;
		if (#compList == 1) then {I}
		else for i from 0 to #compList-1 list (
			sep := getComponentSep(compList,i);
			trim saturate(I,sep)
                     )
             );
   answer := {};
   t := timing for i from 0 to #pdList-1 do
   (
      if (not isSubset(resultSoFar, pdList_i)) then
      (
         answer = append(answer, pdList_i);
	 resultSoFar = intersect(resultSoFar, pdList_i);
      );
   );
   intersectionTime = intersectionTime + t#0;
   (answer, resultSoFar)
)

newPD = method(Options => {Verbosity => 0, Strategy => {}})
newPD(Ideal) := opts -> (I) -> (
   eliminationTime = 0.0;
   sepAndSatTime = 0.0;
   sepAndSatPPDTime = 0.0;
   factorTime = 0.0;
   primaryTime = 0.0;
   splitZeroCleanupTime = 0.0;
   intersectionTime = 0.0;
   retVal := first PDWorker(I, ideal 1_(ring I), 0, opts);
   totalTime := eliminationTime + sepAndSatTime + sepAndSatPPDTime + factorTime + primaryTime + splitZeroCleanupTime + intersectionTime;
   if (opts.Verbosity >= 2) then (
	<< "Time spent on minpoly elimination : " << eliminationTime << endl;
	<< "Time spent on sep and sat         : " << sepAndSatTime << endl;
	<< "Time spent on sep and satPPD      : " << sepAndSatPPDTime << endl;
	<< "Time spent factoring              : " << factorTime << endl;
	<< "Time spent checking primary       : " << primaryTime << endl;
	<< "TIme spent cleaning in splitzero  : " << splitZeroCleanupTime << endl;
	<< "Time spent intersecting           : " << intersectionTime << endl;
	<< "Total of these                    : " << totalTime << endl;
   );
   retVal
)

minSatPPDOur = (I, facs) -> (
     ret1 := minSatPPD(I, facs);
     ret2 := minSatPPD2(I, facs);
     --error "debug me";
     << netList{reverse ret1, reverse ret2} << endl;
     ret1
     )

-- internal subroutine for newPD
PDWorker = method(Options => {Verbosity => 0, Strategy => {}})
PDWorker(Ideal, Ideal, ZZ) := opts -> (I, resultSoFar, callDepth) ->
(
   local retVal;
   local otherComps;
   comps := {};
   newResultSoFar := resultSoFar;
   --printSkip := concatenate (callDepth : ".");
   indSetI := independentSets(I, Limit => 1);
   if (indSetI == {1_(ring I)}) then (
	retVal = primDecZeroDim(I,{},resultSoFar,opts);
      if opts.Verbosity >= 2 then (
         << "ZD Components Found : " << netList retVal#0 << endl
      );
   )
   else
   (
      independentVars := support first indSetI;
      t1 := timing (mySep := first getSeparator(I, independentVars));
      --t2 := timing ((Isat,satIndex) := getSaturation(I,mySep));
      local Isat;
      local satIndex;
      local t2;
      if mySep == 1 then (
         t2 = timing(Isat = I); 
	 satIndex = 0;
	 )
      else (
	 -- this section includes code from the PrimaryDecomposition package  
         --t2 = timing (ret := minSatPPD2(I,factors mySep));
	 << "indep set: " << independentVars;
	 t2 = timing (ret := minSatPPDOur(I,factors mySep));
         satIndex = 1;
         mySep = ret#2;
         Isat = ret#0;
      );
      sepAndSatPPDTime = sepAndSatPPDTime + t1#0 + t2#0;
      if opts.Verbosity >= 2 then (
	 << "Sat Info : " << satIndex << ", " << mySep << endl;
         << "Sep Time : " << t1#0 << endl;
         << "Sat Time : " << t2#0 << endl;
      );
      if (not isSubset(resultSoFar,Isat)) then
      (
	 (comps,newResultSoFar) = primDecZeroDim(Isat, independentVars, resultSoFar, opts);
	 if opts.Verbosity >= 2 then (
            << "Components Found : " << netList comps << endl;
	 );
      )
      else
      (
         if (opts.Verbosity >= 2) then (
	    << "Skipping PD of saturation." << endl;
	 )
      );
      newI := I + ideal (mySep^satIndex);
      if (not isSubset(newResultSoFar,newI)) then
      (
         (otherComps,newResultSoFar) = PDWorker(newI, newResultSoFar, callDepth + 1,opts);
	 comps = join (comps, otherComps)
      );
      retVal = (comps, newResultSoFar);  
   );
   retVal
)

--------------------------------------------------
-- These functions are not being used currently --
--------------------------------------------------

getHighestDegree = method()
getHighestDegree(List, RingElement) := (gs, x) ->
(
   --- the gs are a list of ring elements, and should be polynomials involving (among other things)
   --- the variable x
   --- gets the highest degree element with respect to x.
   first select(gs, g -> degree(x,g) == max apply(gs, h -> degree(x,h)))
)

TEST ///
  restart
  load "newGTZ.m2"
  debug newGTZ
  R = QQ[x,y,z]
  myList = {x^2*y+2*x*y, z^3+x^2*y+x*y*z}
  assert(getHighestDegree(myList, x) == x^2*y+2*x*y)
///


--- not finished
--- do we instead need to carry around an ideal M, not p?
ZPD = method()
ZPD(Ideal, List, RingElement) := (I, myVars, p) ->
(
   --- This function takes an ideal, a set of variables, and a prime number or 0 as input.
   --- We assume that in the ring with the variables not in myVars inverted, I is zero dimensional.
   --- The return value is a primary decomposition of I (a list of primary ideals).
   if (myVars == {}) then I
   else
   (
      allVars := gens ring I;
      myNewVars := take(myVars, #myVars-1);
      lastVar := last myVars;
      gbJ := flatten entries gens gb eliminate (myNewVars, I);
      g := getHighestDegree(gbJ, lastVar);
      --- now need to factor g mod a maximal ideal M in R/M[lastVar] (where M = (p,variables not in myVars?))
      --- factorList will be a list of pairs (a,b) where a is an irred factor of g, and b is its order.
      factorList := {};
      --- Find s such that g^s is in I
      --- still use orderOfElement to do this?
      append apply(factorList, (a,b) -> set ZPD(I + ideal a^b, myNewVars, p))
   )
)

--- not finished
PPD0 = method()
PPD0(Ideal, List, RingElement) := (I, myVars, p) ->
(
   --- This function takes an ideal, a list of variables and a prime number or zero p as input
   --- the coefficient ring of the ring of I is a PID (currently only ZZ or a field will work)
   --- Also, we assume here that I \cap R is p-primary
   --- The output of PPD0 is the primary decomposition of I
   local retVal;
   local firstList;
   --- WARNING: need to get an independent set that contains myVars...
   indSetsI := independentSets (I, Limit => 1);
   if (indSetsI == {1_(ring I)}) then (retVal = ZPD(I,myVars,p);)
   else
   (
      variable := first support first independentSets I;
      myNewVars := toList (set myVars - set {variable});
      mySep := first getSeparator(I, myNewVars, p);
      --- WARNING: Make sure PPD0 returns ideals in the original ring
      retVal = PPD0(I, myNewVars, p);
      --- REMARK:  Be more clever with this computation?  I.e., check if it really must be done?
      if ((ideal mySep + I) =!= ideal (1_(ring I))) then retVal = retVal | PPD0(I + ideal mySep,myVars,p);
      retVal = firstList;
   );
   retVal
)

myIntersect = ideals -> (
   result := ideals_0;
   for i from 1 to #ideals-1 do result = intersect(result,ideals_i);
   result
)

makeIrredundant = method();
makeIrredundant(List) := (idealList) ->
(
   if (idealList == {}) then error "Expected nonempty list.";
   runningIntersection := idealList_0;
   newIdealList := {idealList_0};
   for i from 1 to #idealList-1 do
   (
      tempIntersection := intersect(runningIntersection, idealList_i);
      if (runningIntersection != tempIntersection) then
      (
         newIdealList = append(newIdealList,idealList_i);
	 runningIntersection = tempIntersection;
      );
      i = i + 1;
   );   
   newIdealList
)

--------------------------------------------------
-- End of section of code not being used ---------
--------------------------------------------------

isEqualPDs = method()
isEqualPDs(List, List) := (PD1, PD2) -> (
     -- PD1, PD2 are lists of ideals
     -- we need to take their GB's, change to list of polys, then sort the lists of ideals
     -- then compare for equality
     PD1' := sort apply(PD1, I -> flatten entries gens gb I);
     PD2' := sort apply(PD2, I -> flatten entries gens gb I);
     PD1' == PD2'
     )

isIrredundantPD = method()
isIrredundantPD(Ideal, List) := (I, PD) -> (
     -- test:
     -- I = intersect PD
     -- each elem of PD is primary
     -- each elem of PD is needed
     test1 := I == intersect PD;
     test2 := all(PD, isPrimary);
     test3 := #PD === 1 or all(0..#PD-1, i -> (
	       Pdi := drop(PD, {i,i});
	       I != intersect Pdi
	       ));
     test1 and test2 and test3
     )

testPD = method()
testPD Ideal := (I) -> (
     time newPD1 := newPD(I,Verbosity=>0);
     assert isIrredundantPD(I, newPD1);

     time newPD2 := newPD(ideal(I_*),Verbosity=>0,Strategy=>{GeneralPosition});
     assert isIrredundantPD(I, newPD2);     

     time PD := primaryDecomposition(ideal I_*);
     assert isIrredundantPD(I, PD);

     -- the following needs to be modified to consider non-uniqueness of embedded components
     -- assert isEqualPDs(newPD1, PD);
     -- assert isEqualPDs(newPD2, PD)
     assert(#newPD1 == #PD);
     assert(#newPD2 == #PD);
     )


SLOW = (str) -> null
BENCH = (str) -> null
PDTEST = (str) -> TEST (str | "\n  testPD I\n")

beginDocumentation()

doc ///
  Key
    newGTZ
  Headline
    An implementation of the GTZ primary decomposition algorithm
  Description
   Text
     A small example is below.
   Example
     R = ZZ/32003[a,b,c,h]
     I = ideal(a+b+c,a*b+b*c+a*c,a*b*c-h^3)
     newPD(I, Strategy=>{GeneralPosition})
///

doc ///
  Key
    newPD
  Headline
    Computes a primary decomposition of the input ideal I
  Usage
    newPD(I)
  Inputs
    I : Ideal
  Outputs
    pdList : List 
  Description
   Text
     Below is a brief example.
   Example
     R = ZZ/32003[a,b,c,h]
     I = ideal(a+b+c,a*b+b*c+a*c,a*b*c-h^3)
     newPD(I, Strategy=>{GeneralPosition})
     I = ideal I_*
     newPD(I, Strategy=>{BasicPD})
     I = ideal I_*
     newPD(I)
     I = ideal I_*
     newPD(I, Verbosity=>2)
///

doc ///
  Key
    BasicPD
  Headline
    newPD primary decomposition option.
  Usage
    newPD(I, Strategy=>{BasicPD})
  Description
   Text
     Uses the basic primaryDecomposition code (modulo some small reductions) to find the PD.
///

doc ///
  Key
    GeneralPosition
  Headline
    Option for using a general change of coordinates in newPD
  Usage
    newPD(I, Strategy=>{GeneralPosition})
  Description
   Text
     Uses the general position algorithm to perform the bulk of the primary decomposition work.
///

doc ///
  Key
    getSeparator
  Headline
    Blah
  Usage
    getSeparator(I,independentVars)
  Inputs
    I : Ideal
    independentVars : List
  Outputs
    f : RingElement
  Description
   Text
     Returns an element $f$ such that $I = (I,\ f)\ \cap\ (I\ :\ f^\infty)$.  Some effort is made to find an $\ f\ $ that is
     better for the subsequent primary decomposition computations (i.e. low degree).  
///

needs (newGTZ#"source directory"|"newGTZ/tests.m2")

SLOW ///
  R = QQ[a,b,c,d,e,h]
  I = ideal(
         a+b+c+d+e,
	 d*e+c*d+b*c+a*e+a*b,
	 c*d*e+b*c*d+a*d*e+a*b*e+a*b*c,
	 b*c*d*e+a*c*d*e+a*b*d*e+a*b*c*e+a*b*c*d,
	 a*b*c*d*e-h^5)
///

-- The following takes a bit too long for normal testing
SLOW ///
  R = ZZ/32003[a,b,c,d,e,h]
  I = ideal(
         a+b+c+d+e,
	 d*e+c*d+b*c+a*e+a*b,
	 c*d*e+b*c*d+a*d*e+a*b*e+a*b*c,
	 b*c*d*e+a*c*d*e+a*b*d*e+a*b*c*e+a*b*c*d,
	 a*b*c*d*e-h^5)
///

BENCH ///
-- UNKNOWN - Runs for a very long time on built in version, as well as the 'decompose' version.
-- The GeneralPosition one does indeed run a lot faster though
restart
load "newGTZ.m2"
  R = ZZ/32003[a,b,c,d,e,f,g,h,j,k,l,MonomialOrder=>Lex]
  I = ideal "-2hjk + 4ef + bj + ak,
           -2hjl + 4eg + cj + al,
           -4fhj - 4ehk - djk + 2be + 2af,
           -4ghj - 4ehl - djl + 2ce + 2ag,
           -2dfj - 2dek + ab,
           -2dgj - 2del + ac"
  testPD I
///

BENCH ///
  R = ZZ/32003[x,y,z,t,MonomialOrder=>Lex]
  I = ideal(
   y^2*z+2*x*y*t-2*x-z,
   -x^3*z+4*x*y^2*z+4*x^2*y*t+2*y^3*t+4*x^2-10*y^2+4*x*z-10*y*t+2,
   2*y*z*t+x*t^2-x-2*z,
   -x*z^3+4*y*z^2*t+4*x*z*t^2+2*y*t^3+4*x*z+4*z^2-10*y*t-10*t^2+2)
///


BENCH ///
  --- UNKNOWN - Takes a very long time.
  R = ZZ/32003[a,b,c,d,e,f,h,MonomialOrder=>Lex]
  R = ZZ/32003[a,b,c,d,e,f,h]
  I = ideal(
         a+b+c+d+e+f,
	 a*b+b*c+c*d+d*e+e*f+a*f,
	 a*b*c+b*c*d+c*d*e+d*e*f+e*f*a+f*a*b,
	 a*b*c*d+b*c*d*e+c*d*e*f+d*e*f*a+e*f*a*b+f*a*b*c,
	 a*b*c*d*e+b*c*d*e*f+c*d*e*f*a+d*e*f*a*b+e*f*a*b*c+f*a*b*c*d,
	 a*b*c*d*e*f-h^6)
  testPD I
///

BENCH ///
  R = ZZ/32003[a,b,c,d,e,f,g,h,j,k,l]
  I = ideal(h*j*l-2*e*g+16001*c*j+16001*a*l,h*j*k-2*e*f+16001*b*j+16001*a*k,h*j^2+2*e^2+16001*a*j,d*j^2+2*a*e,g*h*j+e*h*l+8001*d*j*l+16001*c*e+16001*a*g,f*h*j+e*h*k+8001*d*j*k+16001*b*e+16001*a*f
          ,e*g*j+8001*c*j^2+e^2*l,d*g*j+d*e*l+16001*a*c,e*f*j+8001*b*j^2+e^2*k,d*f*j+d*e*k+16001*a*b,d*e*j-a*h*j-16001*a^2,d*e^2-a*e*h-8001*a*d*j,d*g*k*l-c*h*k*l-d*f*l^2+b*h*l^2-2*c*f*g+2*b*g^2-16001
       	  *c^2*k+16001*b*c*l,d*g*k^2-c*h*k^2-d*f*k*l+b*h*k*l-2*c*f^2+2*b*f*g-16001*b*c*k+16001*b^2*l,d*g^2*k-c*g*h*k-d*f*g*l+c*f*h*l-8001*c*d*k*l+8001*b*d*l^2+16001*c^2*f-16001*b*c*g,d*f*g*k-b*g*h*k-
       	  8001*c*d*k^2-d*f^2*l+b*f*h*l+8001*b*d*k*l+16001*b*c*f-16001*b^2*g,c*f*g*k-b*g^2*k-8001*c^2*k^2-c*f^2*l+b*f*g*l-16001*b*c*k*l-8001*b^2*l^2,e^2*g*k+8001*c*e*j*k-e^2*f*l-8001*b*e*j*l,d*g*h*l^2
       	  -c*h^2*l^2-8001*d^2*l^3+2*d*g^3-2*c*g^2*h+16000*c*d*g*l+c^2*h*l-8001*c^3,d*f*h*l^2-b*h^2*l^2-8001*d^2*k*l^2+2*d*f*g^2-2*b*g^2*h+16001*c*d*g*k+16001*c*d*f*l+16001*b*d*g*l+b*c*h*l-8001*b*c^2,
       	  d*f*h*k*l-b*h^2*k*l-8001*d^2*k^2*l+2*d*f^2*g-2*b*f*g*h+16001*c*d*f*k+16001*b*d*g*k-16001*b*c*h*k+16001*b*d*f*l-16001*b^2*h*l-8001*b^2*c,d*f*h*k^2-b*h^2*k^2-8001*d^2*k^3+2*d*f^3-2*b*f^2*h+
       	  16000*b*d*f*k+b^2*h*k-8001*b^3)
///


BENCH ///
  --from ExampleIdeals/DGP.m2
  kk = ZZ/32003
  --butcher (DGP) (up to a change of coordinates, this appears to be Bu_S/Y (Wang2)) x
  R = kk[a,b,c,d,e,f,g,h];
  I = ideal"
    a + c + d - e - h,
    2df + 2cg + 2eh - 2h2 - h - 1,
    3df2 + 3cg2 - 3eh2 + 3h3 + 3h2 - e + 4h,
    6bdg - 6eh2 + 6h3 - 3eh + 6h2 - e + 4h,
    4df3 + 4cg3 + 4eh3 - 4h4 - 6h3 + 4eh - 10h2 - h - 1,
    8bdfg + 8eh3 - 8h4 + 4eh2 - 12h3 + 4eh - 14h2 - 3h - 1,
    12bdg2 + 12eh3 - 12h4 + 12eh2 - 18h3 + 8eh - 14h2 - h - 1,
    -24eh3 + 24h4 - 24eh2 + 36h3 - 8eh + 26h2 + 7h + 1"
  testPD I
///

BENCH  ///
  --from ExampleIdeals/DGP.m2
  kk = ZZ/101
  --gonnet (DGP) (I think this is: Go_S/Y, with change of coordinates) x
  R = kk[a,b,c,d,e,f,g,h,j,k,l,m,n,o,p,q,s];
  I = ideal "
    ag,
    gj + am + np + q,
    bl,
    nq,
    bg + bk + al + lo + lp + b + c,
    ag + ak + jl + bm + bn + go + ko + gp + kp + lq + a + d + f + h + o + p,
    gj + jk + am + an + mo + no + mp + np + gq + kq + e + j + q + s - 1,
    jm + jn + mq + nq,
    jn + mq + 2nq,
    gj + am + 2an + no + np + 2gq + kq + q + s,
    2ag + ak + bn + go + gp + lq + a + d,
    bg + al,
    an + gq,
    2jm + jn + mq,
    gj + jk + am + mo + 2mp + np + e + 2j + q,
    jl + bm + gp + kp + a + f + o + 2p,
    lp + b,
    jn + mq,
    gp + a
    "
  testPD I
///


BENCH ///
  --from ExampleIdeals/DGP.m2
  kk = ZZ/101
  --schwarz (DGP) constructing idempotents in group theory x
  R = kk[a,b,c,d,e,h];
  I = ideal"
    -ab - b2 - 2de - 2ch,
    -ac - 2bc - e2 - 2dh,
    -c2 - ad - 2bd - 2eh,
    -2cd - ae - 2be - h2,
    -d2 - 2ce - ah - 2bh
    "
///

BENCH ///
  --from ExampleIdeals/DGP.m2
  kk = ZZ/101
--dejong (DGP) related to the base space of a semi-universal deformation
-- of a rational quadruple point (same as Theo1, after change of coord) x
R = kk[a,b,c,d,e,f,g,h,j,k,l]
I = ideal"-2hjk + 4ef + bj + ak,
  -2hjl + 4eg + cj + al,
  -4fhj - 4ehk - djk + 2be + 2af,
  -4ghj - 4ehl - djl + 2ce + 2ag,
  -2dfj - 2dek + ab,
  -2dgj - 2del + ac"
///

BENCH ///
  --from ExampleIdeals/DGP.m2
  kk = ZZ/101
--gerdt (DGP, from POSSO)
R = kk[t,u,v,w,x,y,z];
I = ideal"2tw + 2wy - wz,
  2uw2 - 10vw2 + 20w3 - 7tu + 35tv - 70tw,
  6tw2 + 2w2y - 2w2z - 21t2 - 7ty + 7tz,
  2v3 - 4uvw - 5v2w + 6uw2 + 7vw2 - 15w3 - 42vy,
  6tw + 9wy + 2vz - 3wz - 21x,
  9uw3-45vw3+135w4+14tv2-70tuw+196tvw-602tw2-14v2z+28uwz+
    14vwz - 28w2z + 147ux - 735vx + 2205wx - 294ty + 98tz + 294yz - 98z2,
  36tw3+6w3y-9w3z-168t2w-14v2x+28uwx+14vwx-28w2x-28twy+
    42twz + 588tx + 392xy - 245xz,
  2uvw - 6v2w - uw2 + 13vw2 - 5w3 - 28tw + 14wy,
  u2w - 3uvw + 5uw2 - 28tw + 14wy,
  tuw + tvw - 11tw2 - 2vwy + 8w2y + uwz - 3vwz + 5w2z - 21wx,
  5tuw-17tvw+33tw2-7uwy+22vwy-39w2y-2uwz+6vwz-10w2z+63wx,
  20t2w - 12uwx + 30vwx - 15w2x - 10twy - 8twz + 4wyz,
  4t2w - 6uwx + 12vwx - 6w2x + 2twy - 2wy2 - 2twz + wyz,
  8twx + 8wxy - 4wxz"
///

SLOW  ///
  --from ExampleIdeals/DGP.m2
  kk = ZZ/101
  --mikro (DGP) from analyzing analog circuits
  R = kk[a,b,c,d,e,f,g,h]
  I = ideal"
  59ad + 59ah + 59dh - 705d - 1199h,
  330acde + 330aceh + 330cdeh - 407acd - 1642ade - 1410cde 
    - 407ach - 407cdh - 1642aeh - 2398ceh - 1642deh,
  -483acd - 483ach - 483cdh + 821ad + 705cd + 821ah + 1199ch + 821dh,
  13926abcde + 13926abceh + 13926bcdeh - 9404abcd - 9239abde 
    - 4968acde - 13157bcde - 9404abch - 9404bcdh - 9239abeh 
    - 4968aceh - 13025bceh - 9239bdeh - 4968cdeh,
  -cde - 377cdh - ceh - deh,
  -54acf - 54adf + a + d,
  adfg + a + d"
///

SLOW ///
  --from ExampleIdeals/DGP.m2
  kk = ZZ/101
  --amrhein (DGP)
  R = kk[a,b,c,d,e,f];
  I = ideal"
  a2 + d2 + 2ce + 2bf + a,
  2ab + 2de + 2cf + b,
  b2 + 2ac + e2 + 2df + c,
  2bc + 2ad + 2ef + d,
  c2 + 2bd + 2ae + f2 + e,
  2cd + 2be + 2af + f"
///

SLOW ///
  --from ExampleIdeals/DGP.m2
  kk = ZZ/5
  --huneke (DGP)
  R = kk[s,t,u,x,y]
  I = ideal"
  s15,
  t15,
  u15,
  u5 - s3tx + s2t2x + s2t2y - st3y"
///

SLOW ///
  --from ExampleIdeals/DGP.m2
  kk = ZZ/101
  --wang1 (DGP)
  R = kk[a,b,c,d,e,f,g,h,k,l];
  I = ideal"
  f2h-1,
  ek2 - 1,
  g2l - 1,
  2ef2g2hk2 + f2g2h2k2 + 2ef2g2k2l + 2f2g2hk2l + f2g2k2l2 + ck2,
  2e2fg2hk2 +2efg2h2k2 +2e2fg2k2l+4efg2hk2l+2fg2h2k2l+2efg2k2l2
    + 2fg2hk2l2 + 2bfh,
  2e2f2ghk2 +2ef2gh2k2 +2e2f2gk2l+4ef2ghk2l+2f2gh2k2l+2ef2gk2l2
    + 2f2ghk2l2 + 2dgl,
  e2f2g2k2 + 2ef2g2hk2 + 2ef2g2k2l + 2f2g2hk2l + f2g2k2l2 + bf2,
  2e2f2g2hk +2ef2g2h2k +2e2f2g2kl+4ef2g2hkl+2f2g2h2kl+2ef2g2kl2
    + 2f2g2hkl2 + 2cek,
  e2f2g2k2 + 2ef2g2hk2 + f2g2h2k2 + 2ef2g2k2l + 2f2g2hk2l + dg2,
  -e2f2g2hk2-ef2g2h2k2-e2f2g2k2l-2ef2g2hk2l-f2g2h2k2l-ef2g2k2l2
    - f2g2hk2l2 + a2"
///

SLOW ///
  --from ExampleIdeals/DGP.m2
  kk = ZZ/101
  --siebert (DGP)
  R = kk[t,w,x,y,z];
  I = ideal"
  w2xy + w2xz + w2z2,
  tx2y + x2yz + x2z2,
  twy2 + ty2z + y2z2,
  t2wx + t2wz + t2z2"
///

SLOW ///
  --from ExampleIdeals/DGP.m2
  kk = ZZ/101
  --amrheim2 (DGP)
  R = kk[a,b,c,d,e,f,g];
  I = ideal"
  a2 + 2de + 2cf + 2bg + a,
  2ab + e2 + 2df + 2cg + b,
  b2 + 2ac + 2ef + 2dg + c,
  2bc + 2ad + f2 + 2eg + d,
  c2 + 2bd + 2ae + 2fg + e,
  2cd + 2be + 2af + g2 + f,
  d2 + 2ce + 2bf + 2ag + g"
///

SLOW ///
  --from ExampleIdeals/DGP.m2
  kk = ZZ/3
  --huneke2 (not in published DGP) -- over ZZ/3 is real test
  R = kk[x,y,u,s,t];
  I = ideal"
  x27,
  y27,
  u27,
  u5-xy(x-y)(sx-ty)"
///


SLOW ///
  -- DGP Wang
  R = ZZ/32003[a,b,c,d,f,g,h,k,l,s,t,u,v,w,x,y,z]
  I = ideal"
    -ab-ad+2ah,
    ad-bd-cf-2ah+2bh+2ck,
    ab-ad-2bh+2dh-2ck+2fk+2gl,
    ac-2cs-at+2bt,
    ac-cs-2at+bt,
    -d-3s+4u,
    -f-3t+4v,
    -g+4w,
    -a+2x,
    -b2-c2+2bx+2cy,
    -d2-f2-g2+2dx+2fy+2gz"
  testPD I
///

end

TEST ///
  --from ExampleIdeals/DGP.m2
  kk = ZZ/101
///

TEST ///
  --from ExampleIdeals/DGP.m2
  kk = ZZ/101
///



--------------------------------------------------------
--------------------------------------------------------
--------------------------------------------------------
--------------------------------------------------------
--------------------------------------------------------
--------------------------------------------------------
--------------------------------------------------------
--------------------------------------------------------
--katsura4 (DGP, from POSSO)
katsura(4,kk)
--------------------------------------------------------
--katsura5 (DGP, from POSSO)
katsura(5,kk)
--------------------------------------------------------
--cyclic roots 5 homog (DGP)
cyclicRootsHomogeneous(5,kk)
--------------------------------------------------------
--cyclic roots 5 (DGP, from POSSO)
cyclicRoots(5,kk)
--------------------------------------------------------
--cyclic roots 4 (DGP, from POSSO)
cyclicRoots(4,kk)
--------------------------------------------------------
Kahn4
--------------------------------------------------------
Iarrobino
--------------------------------------------------------
Theo0, Theo2, Theo3, Theo4
--------------------------------------------------------
--------------------------------------------------------
--------------------------------------------------------
--------------------------------------------------------
--------------------------------------------------------
--------------------------------------------------------
--------------------------------------------------------
--------------------------------------------------------
--------------------------------------------------------
--------------------------------------------------------
--------------------------------------------------------
--------------------------------------------------------
--------------------------------------------------------
--------------------------------------------------------
--------------------------------------------------------
--------------------------------------------------------
--------------------------------------------------------
  --------------------------------------------------------
--------------------------------------------------------
--------------------------------------------------------


end

restart
path = prepend("/Mac2SVN/M2/Macaulay2/packages", path)
loadPackage "ExampleIdeals"
loadPackage "newGTZ"
I = bayes({{},{1},{1},{2},{3,4}}, (2,2,2,2,2))
I = bayes({{},{},{1},{1,2},{3}}, (2,2,2,2,2))
I = bayes({{}, {1}, {2}, {2}, {2}},(2,2,2,2,2))
I = bayes({{},{1},{2},{3}}, (2,2,2,2))
I = bayes({{},{1},{1},{2,3}}, (2,2,2,2))
I = bayes({{},{1},{1,2},{2,3}}, (2,2,2,2))
I = bayes({{},{1},{2},{2,3}}, (2,2,2,2))
time ourPD3 = newPD(I,Verbosity=>2,Strategy=>{GeneralPosition});
I = ideal flatten entries gens I
time ourPD = newPD(I,Verbosity=>2);

time primaryDecomposition(ideal I_*)

-- This one does better
R = QQ[b,s,t,u,v,w,x,y,z];
minSatPPD(
  ideal"su-bv,tv-sw,vx-uy,wy-vz,w2x2-2uwxz+u2z2,t2y2-2styz+s2z2,s2w,-tuw+bw2,s2t,btu3,s2v,s4".
  {z, x, t, - t*x + b*z, - t*x + 2b*z}
  )

return; continue
netList{reverse ret1, reverse ret2}
I == intersect(ret1#0, I + ideal(ret1#2, ret2#2))


time newPD2 = newPD(ideal(I_*),Verbosity=>2,Strategy=>{GeneralPosition});


debug PrimaryDecomposition
minSatPPD(I, gens R)
use R
J = I + ideal(s*v)

time newPD2 = newPD(ideal(J_*),Verbosity=>2,Strategy=>{GeneralPosition});
