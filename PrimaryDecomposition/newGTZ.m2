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
     testPD,
     PDhelper,
     myPD,
     profilePD,
     singularPD
     }

needsPackage "ExampleIdeals"
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
     -- ret2 := minSatPPD2(I, facs);
     --error "debug me";
     -- << netList{reverse ret1, reverse ret2} << endl;
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
	if opts.Verbosity >= 2 then (
	     << "indep set: " << independentVars;
	     );
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

-- PD1: 
--   input: I             ideal to decompose
--          resultSoFar   ignore any components that are as large as this ideal
--                        (generally this is the intersection of the ideals in compsSoFar)
--          compsSoFar    a list of {prime, primary, indepset, factorlist}
--                        where factorlist is a list of all elements "inverted" to get to this ideal
--   returns: a triple (I', resultSoFar', compsSoFar')
--     where I' is either null, indicating that the PD is complete, or is the next ideal whose PD is to be computed
PDhelper = method(Options => {Verbosity => 0, Strategy => {}})
PDhelper(Ideal, Ideal, List) := opts -> (I, resultSoFar, compsSoFar) -> (
   local retVal;
   local otherComps;
   comps := {};
   newResultSoFar := resultSoFar;
   indSetI := independentSets(I, Limit => 1);
   if (indSetI == {1_(ring I)}) then (
	retVal = primDecZeroDim(I,{},resultSoFar,opts);
      if opts.Verbosity >= 2 then (
         << "ZD Components Found : " << netList retVal#0 << endl;
      return splice(null, retVal);
      );
   );
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
	if opts.Verbosity >= 2 then (
	     << "indep set: " << independentVars;
	     );
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
   if (not isSubset(resultSoFar,Isat)) then (
	if opts.Verbosity >= 3 then (
	     << "about to do ZERODIM" << endl;
	     );
	(comps,newResultSoFar) = primDecZeroDim(Isat, independentVars, resultSoFar, opts);
	if opts.Verbosity >= 2 then (
             << "Components Found : " << netList comps << endl;
	     );
      	)
   else (
	if (opts.Verbosity >= 2) then (
	     << "Skipping PD of saturation." << endl;
	     )
      	);
   if opts.Verbosity >= 3 then (
	<< "about to do RIGHT TREE" << endl;
	);
   newI := I + ideal (mySep^satIndex);
   if (not isSubset(newResultSoFar,newI)) then (
	(newI, newResultSoFar, join(compsSoFar, comps))
	)
   else (
	(null, newResultSoFar, join(compsSoFar, comps))
	)
)

myPD = method(Options => {Verbosity => 0, Strategy => {}})
myPD(Ideal) := opts -> (I) -> (
   eliminationTime = 0.0;
   sepAndSatTime = 0.0;
   sepAndSatPPDTime = 0.0;
   factorTime = 0.0;
   primaryTime = 0.0;
   splitZeroCleanupTime = 0.0;
   intersectionTime = 0.0;
   result := (I, ideal 1_(ring I), {});
   while result#0 =!= null do (
     result = PDhelper(result, opts);
     if opts.Verbosity >= 3 then (
	  << "next return value: " << netList toList result << endl;
	  );
     );
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
   last result
)

gbsize = (Q) -> sum apply(flatten entries gens gb Q, size)

profilePD = method(Options => {Verbosity => 0, Strategy => {}})
profilePD(Ideal) := opts -> (I) -> (
   eliminationTime = 0.0;
   sepAndSatTime = 0.0;
   sepAndSatPPDTime = 0.0;
   factorTime = 0.0;
   primaryTime = 0.0;
   splitZeroCleanupTime = 0.0;
   intersectionTime = 0.0;
   result := (I, ideal 1_(ring I), {});
   t := timing while result#0 =!= null do (
     result = PDhelper(result, opts);
     if opts.Verbosity >= 3 then (
	  << "next return value: " << netList toList result << endl;
	  );
     );
   totalTime := eliminationTime + sepAndSatTime + sepAndSatPPDTime + factorTime + primaryTime + splitZeroCleanupTime + intersectionTime;
   Qs := last result;
   Qs = sort(Qs/(Q -> (codim Q, degree Q, gbsize Q)));
   ({{"Total time", t#0},
	{"Total of these:", totalTime},
	{"  Time spent on minpoly elimination : ", eliminationTime},
	{"  Time spent on sep and sat", sepAndSatTime},
	{"  Time spent on sep and satPPD", sepAndSatPPDTime},
	{"  Time spent factoring", factorTime},
	{"  Time spent checking primary", primaryTime},
	{"  Time spent cleaning in splitzero", splitZeroCleanupTime},
	{"  Time spent intersecting", intersectionTime},
	{"#components", #Qs},
	{"Codim,Degree,Size", Qs}
	}, last result)
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

--------------------------------------------------
-- Link to Singular primary decomposition --------
--------------------------------------------------
primdecStr = ///
LIB "primdec.lib";
list L=primdecGTZ(I1);
L;
link fil=":a @FILE@";
for (int idx=1; idx<=size(L); idx++) {
  for (int jdx=1; jdx<=size(L[idx]); jdx++) {
    write(fil, L[idx][jdx]);
  }}
///
  
singularPD = method()
singularPD Ideal := (I) -> (
     -- checks: I is an ideal in a poly ring.
     -- poly ring has variables usable by Singular
     -- monomial order translates OK.
     -- coeff ring is QQ or ZZ/p.  Perhaps allow others later?
     --
     -- Step 1: Create the ring and ideal for singular
     outfile := "foo-sing.answer";
     ringStr := toSingular ring I;
     idealStr := toSingular I;
     primdec := replace("@FILE@", outfile, primdecStr);
     "foo.sing" << ringStr << endl << idealStr << endl << primdec << endl << close;
     -- Step 2: Append code for prim decomp
     -- Step 3: run Singular (from path)
     if fileExists outfile then removeFile outfile;
     result := get "!Singular <foo.sing";
     -- Step 5: translate output to M2 list of lists of ideals
     answer := apply(lines get outfile, f -> value("ideal\""|f|"\""));
     pack(2,answer)
     )
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

     time newPD2 := myPD(ideal(I_*),Verbosity=>0,Strategy=>{GeneralPosition});
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
needs (newGTZ#"source directory"|"newGTZ/slower-tests.m2")

end



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

fromsingular = ///
[1]:
   [1]:
      _[1]=y
      _[2]=v
      _[3]=s
   [2]:
      _[1]=y
      _[2]=v
      _[3]=s
[2]:
   [1]:
      _[1]=w
      _[2]=v
      _[3]=u
   [2]:
      _[1]=w
      _[2]=v
      _[3]=u
[3]:
   [1]:
      _[1]=-wy+vz
      _[2]=-wx+uz
      _[3]=-vx+uy
      _[4]=-ty+sz
      _[5]=-tv+sw
      _[6]=-tx+bz
      _[7]=-sx+by
      _[8]=-tu+bw
      _[9]=-su+bv
   [2]:
      _[1]=-wy+vz
      _[2]=-wx+uz
      _[3]=-vx+uy
      _[4]=-ty+sz
      _[5]=-tv+sw
      _[6]=-tx+bz
      _[7]=-sx+by
      _[8]=-tu+bw
      _[9]=-su+bv
[4]:
   [1]:
      _[1]=y2
      _[2]=w2
      _[3]=-wy+vz
      _[4]=vy
      _[5]=vw
      _[6]=v2
      _[7]=-vx+uy
      _[8]=uw
      _[9]=uv
      _[10]=u2
      _[11]=sy
      _[12]=-tv+sw
      _[13]=sv
      _[14]=s2
      _[15]=bwy-suz
      _[16]=-su+bv
   [2]:
      _[1]=y
      _[2]=w
      _[3]=v
      _[4]=u
      _[5]=s
///

topoly = (str) -> value ("poly\""|str|"\"")
L1 = drop(separateRegexp(///^\[[0-9]+\]\:///, fromsingular), 1)
L2 = apply(L1, f -> (
	  f1 := drop(separateRegexp(///^ +\[[0-9]+\]\:///, f), 1);
	  apply(f1, f2 -> (
		    f3 := replace(///\_\[[0-9]+\]=///, "", f2);
		    ideal apply(drop(lines f3, 1), topoly)
	       ))))
	  
#oo
o40#1

