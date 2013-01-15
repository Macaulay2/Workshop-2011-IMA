needsPackage "ModularGCD"
needs "quickGB.m2"

gbRationalReconstruction = method()
gbRationalReconstruction (Ideal,List) := (L, paramList) -> (
  -- Input: An ideal L in a ring A over a finite field, and a list of variables paramList that are to be inverted
  -- Output: A list of elements that form a Groebner basis of L in the polynomial ring over a fraction field with the variables
  --         in paramList inverted
  A := ring L;
  kk := coefficientRing A;
  if #paramList === 0 then return (flatten entries gens gb L,1);
  
  evalVar := first paramList;
  newParamList := drop(paramList,1);
  ratResult := null;
  (loopG,loopE) := (null,null);
  loopCount := 0;
  usedCoords := set {};
  totalLoops := 0;
  H := {};
  numBadEvals := 0;
  -- need to rewrite the loop.  ratresult is never reset.
  while ratResult === null do (
    loopCount = loopCount+1;
    -- the next three lines ensure we do not pick the same specialization twice for a coordinate
    a := random kk;
    while member(a,usedCoords) do a = random kk;
    usedCoords = usedCoords + set {a};
    randMap := map(A,A,{evalVar => a});
    (G,subLoops) := gbRationalReconstruction(randMap L,newParamList);
    totalLoops = totalLoops + subLoops;
    -- this code block handles the case when the ideal of lead terms varies by the specialization chosen.
    -- In this case, we should ignore the new value.  If we keep getting bad specializations,
    -- then the initial specialization is probably the bad one, so we reset the loop.
    -- Ask Mike to make sure this is the right thing to do.
    if loopG =!= null and (G / leadTerm != loopG / leadTerm) then (
       numBadEvals = numBadEvals + 1;
       if numBadEvals > 5 then (loopG,loopE) = (null,null) else continue;
    );
    if loopG === null then (loopG, loopE) = (G,evalVar-a) else (
       H = for i from 0 to #G-1 list (
          polyCRA((loopG#i,loopE), (G#i,evalVar-a), evalVar)
       );
       loopG = H / first;
       loopE = last first H;
    );
    rrLoopG := for i from 0 to #loopG-1 list (
       retVal := polyRationalReconstruction(loopG#i,evalVar,loopE);
       if retVal === null then break;
       first retVal
    );
    if #rrLoopG == #loopG then (	 << "(totalLoopCount,loopCount,paramList) : " << (totalLoops,loopCount,#paramList) << endl;
	 return (rrLoopG,totalLoops);
    )
  );
)  

integerContent = method()
integerContent RingElement := f -> (
  -- f is expected to be in a polynomial ring QQ[x_1..x_n]
  -- TODO: rewrite this to use lcms rather than factor
  coeffs := (terms f) / leadCoefficient;
  join ( coeffs / denominator / factor / toList // flatten / toList / first // unique,
         coeffs / numerator / factor / toList // flatten / toList / first // unique)
)

integerContent Ideal := I -> (
  I_* / integerContent // flatten // unique
)

primesList = select(toList (2..2^15), i -> isPrime i and i > 255)

modPFracGB = method(Options => {"NumSameRecons" => 3})
modPFracGB (Ideal,List) := opts -> (I, baseVars) -> (
  -- Input: An ideal I over a polynomial ring defined over QQ, and a list baseVars of variables
  --        which will be inverted
  -- Output: A gb of I over the polynomial ring over the fraction field with baseVars inverted

  S := ring I;
  SZ := ZZ(monoid S);
  intCont := if char ring I == 0 then integerContent I else {};
  -- TODO: check using lcm and divisions instead, not my 'content'
  validPrimes := random toList (set primesList - set intCont);
  
  i := 0;
  reconTally := new MutableHashTable;
  continueLoop := true;
  IpRatReconQ := null;
  baseVars = toList((set support I) * (set baseVars)); -- we only need to consider variables which actually occur in gens of I
  while #reconTally == 0 or reconTally#(IpRatReconQ_*) < opts#"NumSameRecons" do (
    if char ring I != 0 then (   -- if nonzero char, just do rational reconstruction over Zp.
       IpRatReconQ = ideal first gbRationalReconstruction(I,baseVars);
    )
    else (  -- otherwise, reconstruct over Zp, then do integer reconstruction
       p := validPrimes_i;
       Sp := (ZZ/p)(monoid S);
       phi := map(Sp,S);
       Ip := phi I;
       IpRatRecon := ideal first gbRationalReconstruction(Ip,baseVars / phi);
       IpRatReconQ = integerRationalReconstruction(sub(IpRatRecon,SZ),p);
       i = i + 1;
    );
    if reconTally#?(IpRatReconQ_*) then reconTally#(IpRatReconQ_*) = reconTally#(IpRatReconQ_*) + 1 else reconTally#(IpRatReconQ_*) = 1;
  );
  sub(IpRatReconQ,S)
)

--- not sure if the below should return a list of sequences or a list of lists
--- a few commands to make cartesian product of lists easier (and faster than using toList and set!)
List ** List := (xs,ys) -> flatten for y in ys list apply(xs, x -> {x,y})
-- compose all functions in a list
composeList := fs -> if #fs == 0 then identity else (first fs) @@ (composeList drop(fs,1))
-- left, rather than right, fold.
-- takes the iterated cartesian product of a List of Lists.  Care is taken
-- to avoid flattening all the way, since the original list may be a list of lists.
cartProdList = method()
cartProdList List := xss -> (
    if #xss < 2 then return xss;
    if #xss == 2 then return (first xss) ** (last xss); 
    xsLengths := xss / length / (i -> toList(0..(i-1)));
    indexList := fold((as,bs) -> (as ** bs) / flatten,xsLengths);
    apply(indexList, l -> apply(#l, i -> xss#i#(l#i)))
)

factorListToIdeal = method()
factorListToIdeal List := facs -> ideal gens gb ideal apply(facs, p -> (p#1)^(p#0))

idealToFactorList = method()
idealToFactorList Ideal := I -> flatten (I_* / factors / (l -> l / toList))

factorTower = method(Options => {Verbosity => 0})
factorTower List := opts -> polyList -> (
   polyFacList := for f in polyList list ((factors f) / toList);
   splitFacList := cartProdList polyFacList;
   -- before calling factorIrredTower, do I need to make sure the ideal is zero dimensional over the base field? Ignore for now.
   flatten apply(splitFacList, facs -> factorIrredTower(facs,opts))
)
factorTower Ideal := opts -> I -> factorTower(I_*,opts) / factorListToIdeal

factorIrredTower = method(Options => options factorTower)
factorIrredTower List := opts -> polyList -> (
    -- Input  : IF = factorListToIdeal polyList is an ideal of k(basevars)[fibervars] and should be in a ring returned by makeFiberRings
    --          IF should satisfy:
    --            1. IF is zero-dimensional
    --            2. IF_* is a lex GB for IF (in ascending order of leadterms)
    --            3. IF_* only contains (hopefully!) elements whose lead term is a pure power.
    --            4. polyList is a list of lists whose first entry is a power, and whose last entry is an irreducible over k(vasevars)

    -- Output : A list of lists.  The intersection of the ideals generated by each list is IF, and for each ideal IF_j in the
    --          list, IF_j = (f_1,...,f_k) where (after ignoring linear terms that are removed and then reinserted)
    --               f_1 is an irreducible monic polynomial in k(basevars)[x_1] (where x_1 is the
    --                 least variable of fibervars that did not appear linearly in IF)
    --               f_2 is an irreducible monic polynomial in k(basevars)[x_1,x_2]/(f_1) (where x_2 is 
    --                 least variable of fibervars that did not appear linearly in IF other than x_1)
    --               ...
    --               f_k is an irreducible monic polynomial in k(basevars)[x_1,...,x_k]/(f_1,...,f_{k-1})

    -- partition the generators into linear and nonlinear terms
    E := partition(p -> hasLinearLeadTerm(p#1 // leadCoefficient p#1), polyList);
    -- nothing to do, all linear generators
    if not E#?false then return {polyList};
    nonlinears := E#false;
    if #nonlinears <= 1 then return {polyList};
    -- keep for later - we will take them out of the computation and reinsert them.
    linears := if E#?true then E#true else {};

    -- here, we are using that nonlinears_0 is irreducible over the fraction field.
    retVal := {{nonlinears_0}};
    for i from 1 to #nonlinears - 1 do (
       retVal = flatten apply(retVal, K -> factorIrredTowerWorker(K | {nonlinears_i}, opts));
    );
    retVal / (C -> linears | C)
)
factorIrredTower Ideal := opts -> I -> (factorIrredTower idealToFactorList I_*) / factorListToIdeal

factorIrredTowerWorker = method(Options => options factorTower)
factorIrredTowerWorker List := opts -> polyList -> (
    -- this is the worker function for the above function.  It assumes everything
    -- assumed above, as well as that the generators of the input form a 'chain' of irreducibles
    -- except for the last element.
    vecdim := polyList/(p -> (first degree leadTerm p#1) * p#0)//product;  -- the vector space dimension of the extension of k(basevars) that the irred ideal gives
    IF := factorListToIdeal polyList;
    L := ideal (IF_* / numerator);
    S := ring L;
    SF := ring IF;
    varsList := IF_* / leadTerm / support // flatten;
    lastVar := varsList#0; -- this is the smallest variable in the monomial order
    otherVars := drop(varsList, 1); 
    F := sum apply(otherVars, x -> (1 + random 10) * x);
    IF1 := sub(IF, lastVar => lastVar + F);
    L1 := ideal(IF1_*/numerator);
    lastVar = numerator lastVar;
    otherVars = otherVars/numerator;
    -- as of now, we use quickGB if the base field is not a fraction field.
    -- use modPFracGB here too perhaps?
    G := time if numgens coefficientRing S == 0 then
                 (quickEliminate(L1,otherVars))_0
              else
                 (eliminate(L1, otherVars))_0;
    completelySplit := degree(lastVar, G) === vecdim;
    facs := factors G;
    if opts.Verbosity > 0 then print netList facs;
    F = numerator F;
    facs1 := apply(facs, (mult,h) -> (mult,sub(h, lastVar => lastVar - F)));
    newFacs := 1_SF;
    lastIrred := IF_(numgens IF - 1);
    -- sort the factors (by degree) and only compute GB for the first n-1 of them
    facs1 = (sort apply(#facs1, i -> (first degree facs1#i#1,facs1#i))) / last;
    -- select the factors which are nonunits of SF
    facs1 = select(facs1, f -> not isUnit(S.cache#"StoSF" f#1));
    --- need to alter this to handle primary case - not sure how to get power of irreducible from the factor efficiently 
    if #facs1 == 0 then {polyList}
    else if (#facs1 == 1 and facs1#0#0 == 1) then {polyList}
    else (
         j := 0;
         -- Note that the second condition forces the 'last factor' trick to not occur
         -- in case the polynomial is, for example, a pure power of an irreducible (modulo the earlier polynomials, of course)
         retVal := flatten while (j <= #facs1 - 2 or (j == #facs1-1 and facs1#j#0 > 1)) list (
                      fac := facs1#j;
                      j = j + 1;
                      G = (fac#1) % L;
                      if G == 0 then error "Internal error.  Tried to add in zero element to ideal in factorTower.";
                      C := time ideal gens gb S.cache#"StoSF" modPFracGB(ideal G + L,gens coefficientRing SF / S.cache#"SFtoS");
                      if C == 1 then continue;
                      newFacs = newFacs * (first toList (set C_* - set IF_*))^(fac#0);
                      -- now we need to put the power of the new irreducible in, if it exists (and if minprimes is not set)
                      -- TODO: Prove that this power is correct?
                      C = idealToFactorList C;
                      C = drop(C,-1) | {{fac#0,(last C)#1}};
                      if completelySplit then {C} else factorIrredTower C
                   );
         -- if we made it all the way through facs1, then we are done.  Else, we may use
         -- the previous computations to determine the final factor
         if j == #facs1 then retVal
         else (
            lastFactor := lastIrred // newFacs;
            lastComp := flatten ((flatten entries gens gb ((S.cache#"StoSF" L) + lastFactor)) / factors / (l -> l / toList));
            -- TODO: Check for completelySplit here too.
            if completelySplit then append(retVal, lastComp) else join(retVal,factorIrredTower lastComp)
        )
    )
)

end

--- making sure the cartesian product stuff is working
restart
debug needsPackage "PD"
needsPackage "ModularGCD"
X = toList (0..1);
X = X ** X
time cartProdList {X,X};
#oo
time cartProdList {X,X,X};
#oo
time cartProdList {X,X,X,X};
#oo
time cartProdList {X,X,X,X,X};
#oo

--- example for factorTower
restart
debug needsPackage "PD"
R = QQ[t,s,r]
(S,SF) = makeFiberRings({},R)
use S
f = r^2-2
g = s^4-4
factorTower {f,g}

--- note:  the example I was worried about, of the form:
--- {f,g} where f is irred and g factors over kk[x]/(f) as g_1^2
--- is not possible as long as kk is perfect.  Forgot about that!

--- a very baby example for factorTower
restart
debug needsPackage "PD"
R = QQ[r,s]
(S,SF) = makeFiberRings({},R)
use S
f = r^2-3
g = s^2+5*s+22/4
factorTower {f,g}
factorTower {f^2,g}
factorTower {f^2,g}
gbTrace = 3
-- problem here, caught in an infinite loop.
factorTower({f^2,g^2},"SplitIrred"=>true, "Minprimes"=>false)
primaryDecomposition ideal {f^2,g^2}

use S
I = ideal {f^2,g^2}
J = ideal {g^2,(r+2*s+5)^2}
K = ideal {g^2,(r-2*s-5)^2}
intersect {J,K} == I

--- another
restart
debug needsPackage "PD"
R = QQ[z,y]
(S,SF) = makeFiberRings({},R)
use S
f = z^2+1
g = y^3+3*y^2*z-3*y-z
-- we have a problem!
factorTower({f,g},"SplitIrred"=>true, "Minprimes"=>true)
splitTower ideal {f,g}

-- Testing modPFracGB
  restart
  debug needsPackage "PD"
  --load "gbRatRecon.m2"
  needsPackage "ModularGCD"
  Q = QQ[e_1, e_2, e_3, e_4, g_1, g_2, g_3, g_4, r]
  (S,SF) = makeFiberRings {e_4,g_1}
  use S
  m1 = r^2-3
  m2 = g_4^4+((4*e_4^2+3*g_1^2)/3)*g_4^2+(4*e_4^4+18*e_4^2*g_1^2)/9
  m3 = g_2^2+(9/8)*g_4^2+(2*e_4^2+9*g_1^2)/8
  fac = 43046721*g_2^8+191318760*g_2^7*g_4-38263752*g_2^7*r+372008700*g_2^6*g_4^2-148803480*g_2^6*g_4*r+14880348*g_2^6*r^2-50664042*g_2^6*e_4^2-239148450*g_2^6*e_4*g_1+(493708689/4)*g_2^6*g_1^2-6377292*g_2^6+413343000*g_2^5*g_4^3-248005800*g_2^5*g_4^2*r+49601160*g_2^5*g_4*r^2-168880140*g_2^5*g_4*e_4^2-797161500*g_2^5*g_4*e_4*g_1+(822847815/2)*g_2^5*g_4*g_1^2-21257640*g_2^5*g_4-3306744*g_2^5*r^3+33776028*g_2^5*r*e_4^2+159432300*g_2^5*r*e_4*g_1-(164569563/2)*g_2^5*r*g_1^2+4251528*g_2^5*r+287043750*g_2^4*g_4^4-229635000*g_2^4*g_4^3*r+68890500*g_2^4*g_4^2*r^2-234555750*g_2^4*g_4^2*e_4^2-1107168750*g_2^4*g_4^2*e_4*g_1+(2285688375/4)*g_2^4*g_4^2*g_1^2-29524500*g_2^4*g_4^2-9185400*g_2^4*g_4*r^3+93822300*g_2^4*g_4*r*e_4^2+442867500*g_2^4*g_4*r*e_4*g_1-(457137675/2)*g_2^4*g_4*r*g_1^2+11809800*g_2^4*g_4*r+459270*g_2^4*r^4-9382230*g_2^4*r^2*e_4^2-44286750*g_2^4*r^2*e_4*g_1+(91427535/4)*g_2^4*r^2*g_1^2-1180980*g_2^4*r^2+(115580763/2)*g_2^4*e_4^4+106977105*g_2^4*e_4^3*g_1+(918266625/2)*g_2^4*e_4^2*g_1^2+1876446*g_2^4*e_4^2-(1979027235/4)*g_2^4*e_4*g_1^3+8857350*g_2^4*e_4*g_1+(7575599601/64)*g_2^4*g_1^4-(18285507/4)*g_2^4*g_1^2+354294*g_2^4+127575000*g_2^3*g_4^5-127575000*g_2^3*g_4^4*r+51030000*g_2^3*g_4^3*r^2-173745000*g_2^3*g_4^3*e_4^2-820125000*g_2^3*g_4^3*e_4*g_1+423275625*g_2^3*g_4^3*g_1^2-21870000*g_2^3*g_4^3-10206000*g_2^3*g_4^2*r^3+104247000*g_2^3*g_4^2*r*e_4^2+492075000*g_2^3*g_4^2*r*e_4*g_1-253965375*g_2^3*g_4^2*r*g_1^2+13122000*g_2^3*g_4^2*r+1020600*g_2^3*g_4*r^4-20849400*g_2^3*g_4*r^2*e_4^2-98415000*g_2^3*g_4*r^2*e_4*g_1+50793075*g_2^3*g_4*r^2*g_1^2-2624400*g_2^3*g_4*r^2+128423070*g_2^3*g_4*e_4^4+237726900*g_2^3*g_4*e_4^3*g_1+1020296250*g_2^3*g_4*e_4^2*g_1^2+4169880*g_2^3*g_4*e_4^2-1099459575*g_2^3*g_4*e_4*g_1^3+19683000*g_2^3*g_4*e_4*g_1+(4208666445/16)*g_2^3*g_4*g_1^4-10158615*g_2^3*g_4*g_1^2+787320*g_2^3*g_4-40824*g_2^3*r^5+1389960*g_2^3*r^3*e_4^2+6561000*g_2^3*r^3*e_4*g_1-3386205*g_2^3*r^3*g_1^2+174960*g_2^3*r^3-25684614*g_2^3*r*e_4^4-47545380*g_2^3*r*e_4^3*g_1-204059250*g_2^3*r*e_4^2*g_1^2-833976*g_2^3*r*e_4^2+219891915*g_2^3*r*e_4*g_1^3-3936600*g_2^3*r*e_4*g_1-(841733289/16)*g_2^3*r*g_1^4+2031723*g_2^3*r*g_1^2-157464*g_2^3*r+35437500*g_2^2*g_4^6-42525000*g_2^2*g_4^5*r+21262500*g_2^2*g_4^4*r^2-72393750*g_2^2*g_4^4*e_4^2-341718750*g_2^2*g_4^4*e_4*g_1+(705459375/4)*g_2^2*g_4^4*g_1^2-9112500*g_2^2*g_4^4-5670000*g_2^2*g_4^3*r^3+57915000*g_2^2*g_4^3*r*e_4^2+273375000*g_2^2*g_4^3*r*e_4*g_1-141091875*g_2^2*g_4^3*r*g_1^2+7290000*g_2^2*g_4^3*r+850500*g_2^2*g_4^2*r^4-17374500*g_2^2*g_4^2*r^2*e_4^2-82012500*g_2^2*g_4^2*r^2*e_4*g_1+(84655125/2)*g_2^2*g_4^2*r^2*g_1^2-2187000*g_2^2*g_4^2*r^2+107019225*g_2^2*g_4^2*e_4^4+198105750*g_2^2*g_4^2*e_4^3*g_1+850246875*g_2^2*g_4^2*e_4^2*g_1^2+3474900*g_2^2*g_4^2*e_4^2-(1832432625/2)*g_2^2*g_4^2*e_4*g_1^3+16402500*g_2^2*g_4^2*e_4*g_1+(7014444075/32)*g_2^2*g_4^2*g_1^4-(16931025/2)*g_2^2*g_4^2*g_1^2+656100*g_2^2*g_4^2-68040*g_2^2*g_4*r^5+2316600*g_2^2*g_4*r^3*e_4^2+10935000*g_2^2*g_4*r^3*e_4*g_1-5643675*g_2^2*g_4*r^3*g_1^2+291600*g_2^2*g_4*r^3-42807690*g_2^2*g_4*r*e_4^4-79242300*g_2^2*g_4*r*e_4^3*g_1-340098750*g_2^2*g_4*r*e_4^2*g_1^2-1389960*g_2^2*g_4*r*e_4^2+366486525*g_2^2*g_4*r*e_4*g_1^3-6561000*g_2^2*g_4*r*e_4*g_1-(1402888815/16)*g_2^2*g_4*r*g_1^4+3386205*g_2^2*g_4*r*g_1^2-262440*g_2^2*g_4*r+2268*g_2^2*r^6-115830*g_2^2*r^4*e_4^2-546750*g_2^2*r^4*e_4*g_1+(1128735/4)*g_2^2*r^4*g_1^2-14580*g_2^2*r^4+4280769*g_2^2*r^2*e_4^4+7924230*g_2^2*r^2*e_4^3*g_1+34009875*g_2^2*r^2*e_4^2*g_1^2+138996*g_2^2*r^2*e_4^2-(73297305/2)*g_2^2*r^2*e_4*g_1^3+656100*g_2^2*r^2*e_4*g_1+(280577763/32)*g_2^2*r^2*g_1^4-(677241/2)*g_2^2*r^2*g_1^2+26244*g_2^2*r^2-(50471421/2)*g_2^2*e_4^6-(198509535/2)*g_2^2*e_4^5*g_1+(604425933/16)*g_2^2*e_4^4*g_1^2+8425323*g_2^2*e_4^4-(4107950235/8)*g_2^2*e_4^3*g_1^3-17926110*g_2^2*e_4^3*g_1+(22097332251/32)*g_2^2*e_4^2*g_1^4+25135839*g_2^2*e_4^2*g_1^2+69498*g_2^2*e_4^2-(4813007445/16)*g_2^2*e_4*g_1^5-(16719615/2)*g_2^2*e_4*g_1^3+328050*g_2^2*e_4*g_1+(1371413025/32)*g_2^2*g_1^6+(2857437/32)*g_2^2*g_1^4-(677241/4)*g_2^2*g_1^2-8748*g_2^2+5625000*g_2*g_4^7-7875000*g_2*g_4^6*r+4725000*g_2*g_4^5*r^2-16087500*g_2*g_4^5*e_4^2-75937500*g_2*g_4^5*e_4*g_1+(78384375/2)*g_2*g_4^5*g_1^2-2025000*g_2*g_4^5-1575000*g_2*g_4^4*r^3+16087500*g_2*g_4^4*r*e_4^2+75937500*g_2*g_4^4*r*e_4*g_1-(78384375/2)*g_2*g_4^4*r*g_1^2+2025000*g_2*g_4^4*r+315000*g_2*g_4^3*r^4-6435000*g_2*g_4^3*r^2*e_4^2-30375000*g_2*g_4^3*r^2*e_4*g_1+15676875*g_2*g_4^3*r^2*g_1^2-810000*g_2*g_4^3*r^2+39636750*g_2*g_4^3*e_4^4+73372500*g_2*g_4^3*e_4^3*g_1+314906250*g_2*g_4^3*e_4^2*g_1^2+1287000*g_2*g_4^3*e_4^2-339339375*g_2*g_4^3*e_4*g_1^3+6075000*g_2*g_4^3*e_4*g_1+(1298971125/16)*g_2*g_4^3*g_1^4-3135375*g_2*g_4^3*g_1^2+243000*g_2*g_4^3-37800*g_2*g_4^2*r^5+1287000*g_2*g_4^2*r^3*e_4^2+6075000*g_2*g_4^2*r^3*e_4*g_1-3135375*g_2*g_4^2*r^3*g_1^2+162000*g_2*g_4^2*r^3-23782050*g_2*g_4^2*r*e_4^4-44023500*g_2*g_4^2*r*e_4^3*g_1-188943750*g_2*g_4^2*r*e_4^2*g_1^2-772200*g_2*g_4^2*r*e_4^2+203603625*g_2*g_4^2*r*e_4*g_1^3-3645000*g_2*g_4^2*r*e_4*g_1-(779382675/16)*g_2*g_4^2*r*g_1^4+1881225*g_2*g_4^2*r*g_1^2-145800*g_2*g_4^2*r+2520*g_2*g_4*r^6-128700*g_2*g_4*r^4*e_4^2-607500*g_2*g_4*r^4*e_4*g_1+(627075/2)*g_2*g_4*r^4*g_1^2-16200*g_2*g_4*r^4+4756410*g_2*g_4*r^2*e_4^4+8804700*g_2*g_4*r^2*e_4^3*g_1+37788750*g_2*g_4*r^2*e_4^2*g_1^2+154440*g_2*g_4*r^2*e_4^2-40720725*g_2*g_4*r^2*e_4*g_1^3+729000*g_2*g_4*r^2*e_4*g_1+(155876535/16)*g_2*g_4*r^2*g_1^4-376245*g_2*g_4*r^2*g_1^2+29160*g_2*g_4*r^2-(84119035/3)*g_2*g_4*e_4^6-110283075*g_2*g_4*e_4^5*g_1+(335792185/8)*g_2*g_4*e_4^4*g_1^2+9361470*g_2*g_4*e_4^4-(2282194575/4)*g_2*g_4*e_4^3*g_1^3-19917900*g_2*g_4*e_4^3*g_1+(12276295695/16)*g_2*g_4*e_4^2*g_1^4+27928710*g_2*g_4*e_4^2*g_1^2+77220*g_2*g_4*e_4^2-(2673893025/8)*g_2*g_4*e_4*g_1^5-9288675*g_2*g_4*e_4*g_1^3+364500*g_2*g_4*e_4*g_1+(761896125/16)*g_2*g_4*g_1^6+(1587465/16)*g_2*g_4*g_1^4-(376245/2)*g_2*g_4*g_1^2-9720*g_2*g_4-72*g_2*r^7+5148*g_2*r^5*e_4^2+24300*g_2*r^5*e_4*g_1-(25083/2)*g_2*r^5*g_1^2+648*g_2*r^5-317094*g_2*r^3*e_4^4-586980*g_2*r^3*e_4^3*g_1-2519250*g_2*r^3*e_4^2*g_1^2-10296*g_2*r^3*e_4^2+2714715*g_2*r^3*e_4*g_1^3-48600*g_2*r^3*e_4*g_1-(10391769/16)*g_2*r^3*g_1^4+25083*g_2*r^3*g_1^2-1944*g_2*r^3+(16823807/3)*g_2*r*e_4^6+22056615*g_2*r*e_4^5*g_1-(67158437/8)*g_2*r*e_4^4*g_1^2-1872294*g_2*r*e_4^4+(456438915/4)*g_2*r*e_4^3*g_1^3+3983580*g_2*r*e_4^3*g_1-(2455259139/16)*g_2*r*e_4^2*g_1^4-5585742*g_2*r*e_4^2*g_1^2-15444*g_2*r*e_4^2+(534778605/8)*g_2*r*e_4*g_1^5+1857735*g_2*r*e_4*g_1^3-72900*g_2*r*e_4*g_1-(152379225/16)*g_2*r*g_1^6-(317493/16)*g_2*r*g_1^4+(75249/2)*g_2*r*g_1^2+1944*g_2*r+390625*g_4^8-625000*g_4^7*r+437500*g_4^6*r^2-(4468750/3)*g_4^6*e_4^2-7031250*g_4^6*e_4*g_1+(14515625/4)*g_4^6*g_1^2-187500*g_4^6-175000*g_4^5*r^3+1787500*g_4^5*r*e_4^2+8437500*g_4^5*r*e_4*g_1-(8709375/2)*g_4^5*r*g_1^2+225000*g_4^5*r+43750*g_4^4*r^4-893750*g_4^4*r^2*e_4^2-4218750*g_4^4*r^2*e_4*g_1+(8709375/4)*g_4^4*r^2*g_1^2-112500*g_4^4*r^2+(33030625/6)*g_4^4*e_4^4+10190625*g_4^4*e_4^3*g_1+(262421875/6)*g_4^4*e_4^2*g_1^2+178750*g_4^4*e_4^2-(188521875/4)*g_4^4*e_4*g_1^3+843750*g_4^4*e_4*g_1+(721650625/64)*g_4^4*g_1^4-(1741875/4)*g_4^4*g_1^2+33750*g_4^4-7000*g_4^3*r^5+(715000/3)*g_4^3*r^3*e_4^2+1125000*g_4^3*r^3*e_4*g_1-580625*g_4^3*r^3*g_1^2+30000*g_4^3*r^3-(13212250/3)*g_4^3*r*e_4^4-8152500*g_4^3*r*e_4^3*g_1-(104968750/3)*g_4^3*r*e_4^2*g_1^2-143000*g_4^3*r*e_4^2+37704375*g_4^3*r*e_4*g_1^3-675000*g_4^3*r*e_4*g_1-(144330125/16)*g_4^3*r*g_1^4+348375*g_4^3*r*g_1^2-27000*g_4^3*r+700*g_4^2*r^6-35750*g_4^2*r^4*e_4^2-168750*g_4^2*r^4*e_4*g_1+(348375/4)*g_4^2*r^4*g_1^2-4500*g_4^2*r^4+1321225*g_4^2*r^2*e_4^4+2445750*g_4^2*r^2*e_4^3*g_1+10496875*g_4^2*r^2*e_4^2*g_1^2+42900*g_4^2*r^2*e_4^2-(22622625/2)*g_4^2*r^2*e_4*g_1^3+202500*g_4^2*r^2*e_4*g_1+(86598075/32)*g_4^2*r^2*g_1^4-(209025/2)*g_4^2*r^2*g_1^2+8100*g_4^2*r^2-(420595175/54)*g_4^2*e_4^6-(61268375/2)*g_4^2*e_4^5*g_1+(1678960925/144)*g_4^2*e_4^4*g_1^2+(7801225/3)*g_4^2*e_4^4-(1267885875/8)*g_4^2*e_4^3*g_1^3-5532750*g_4^2*e_4^3*g_1+(6820164275/32)*g_4^2*e_4^2*g_1^4+7757975*g_4^2*e_4^2*g_1^2+21450*g_4^2*e_4^2-(1485496125/16)*g_4^2*e_4*g_1^5-(5160375/2)*g_4^2*e_4*g_1^3+101250*g_4^2*e_4*g_1+(423275625/32)*g_4^2*g_1^6+(881925/32)*g_4^2*g_1^4-(209025/4)*g_4^2*g_1^2-2700*g_4^2-40*g_4*r^7+2860*g_4*r^5*e_4^2+13500*g_4*r^5*e_4*g_1-(13935/2)*g_4*r^5*g_1^2+360*g_4*r^5-(528490/3)*g_4*r^3*e_4^4-326100*g_4*r^3*e_4^3*g_1-(4198750/3)*g_4*r^3*e_4^2*g_1^2-5720*g_4*r^3*e_4^2+1508175*g_4*r^3*e_4*g_1^3-27000*g_4*r^3*e_4*g_1-(5773205/16)*g_4*r^3*g_1^4+13935*g_4*r^3*g_1^2-1080*g_4*r^3+(84119035/27)*g_4*r*e_4^6+12253675*g_4*r*e_4^5*g_1-(335792185/72)*g_4*r*e_4^4*g_1^2-(3120490/3)*g_4*r*e_4^4+(253577175/4)*g_4*r*e_4^3*g_1^3+2213100*g_4*r*e_4^3*g_1-(1364032855/16)*g_4*r*e_4^2*g_1^4-3103190*g_4*r*e_4^2*g_1^2-8580*g_4*r*e_4^2+(297099225/8)*g_4*r*e_4*g_1^5+1032075*g_4*r*e_4*g_1^3-40500*g_4*r*e_4*g_1-(84655125/16)*g_4*r*g_1^6-(176385/16)*g_4*r*g_1^4+(41805/2)*g_4*r*g_1^2+1080*g_4*r+r^8-(286/3)*r^6*e_4^2-450*r^6*e_4*g_1+(929/4)*r^6*g_1^2-12*r^6+(52849/6)*r^4*e_4^4+16305*r^4*e_4^3*g_1+(419875/6)*r^4*e_4^2*g_1^2+286*r^4*e_4^2-(301635/4)*r^4*e_4*g_1^3+1350*r^4*e_4*g_1+(1154641/64)*r^4*g_1^4-(2787/4)*r^4*g_1^2+54*r^4-(16823807/54)*r^2*e_4^6-(2450735/2)*r^2*e_4^5*g_1+(67158437/144)*r^2*e_4^4*g_1^2+(312049/3)*r^2*e_4^4-(50715435/8)*r^2*e_4^3*g_1^3-221310*r^2*e_4^3*g_1+(272806571/32)*r^2*e_4^2*g_1^4+310319*r^2*e_4^2*g_1^2+858*r^2*e_4^2-(59419845/16)*r^2*e_4*g_1^5-(206415/2)*r^2*e_4*g_1^3+4050*r^2*e_4*g_1+(16931025/32)*r^2*g_1^6+(35277/32)*r^2*g_1^4-(8361/4)*r^2*g_1^2-108*r^2+(13841287201/1296)*e_4^8-(201768035/12)*e_4^7*g_1+(15270722551/144)*e_4^6*g_1^2-(16823807/18)*e_4^6-(307861365/2)*e_4^5*g_1^3-(7352205/2)*e_4^5*g_1+(19575431101/64)*e_4^4*g_1^4+(67158437/48)*e_4^4*g_1^2+(158547/2)*e_4^4-(5822807445/16)*e_4^3*g_1^5-(152146305/8)*e_4^3*g_1^3+146745*e_4^3*g_1+(6506270325/32)*e_4^2*g_1^6+(818419713/32)*e_4^2*g_1^4+(1259625/2)*e_4^2*g_1^2-2574*e_4^2-(843908625/16)*e_4*g_1^7-(178259535/16)*e_4*g_1^5-(2714715/4)*e_4*g_1^3-12150*e_4*g_1+(332150625/64)*g_1^8+(50793075/32)*g_1^6+(10391769/64)*g_1^4+(25083/4)*g_1^2+81
  facModL = -221169825*g_2*g_4^3*e_4^3*g_1-1205128125*g_2*g_4^3*e_4^2*g_1^2+51993540*g_2*g_4^3*e_4^2-(566678025/16)*g_2*g_4^3*e_4*g_1^3+224957250*g_2*g_4^3*e_4*g_1+(66344535/2)*g_2*g_4^3*g_1^2-1713960*g_2*g_4^3-1409400*g_2*g_4^2*r*e_4^4+343947465*g_2*g_4^2*r*e_4^3*g_1+244310100*g_2*g_4^2*r*e_4^2*g_1^2-12556800*g_2*g_4^2*r*e_4^2+(1313107605/16)*g_2*g_4^2*r*e_4*g_1^3-3134700*g_2*g_4^2*r*e_4*g_1-(62964225/8)*g_2*g_4^2*r*g_1^4-2856600*g_2*g_4^2*r*g_1^2-147446550*g_2*g_4*e_4^5*g_1-160683750*g_2*g_4*e_4^4*g_1^2+34662360*g_2*g_4*e_4^4-(5496968475/8)*g_2*g_4*e_4^3*g_1^3+75386700*g_2*g_4*e_4^3*g_1-723076875*g_2*g_4*e_4^2*g_1^4+191254545*g_2*g_4*e_4^2*g_1^2-1142640*g_2*g_4*e_4^2-(1700034075/16)*g_2*g_4*e_4*g_1^5+178556400*g_2*g_4*e_4*g_1^3-2916000*g_2*g_4*e_4*g_1+(246024675/8)*g_2*g_4*g_1^4-856980*g_2*g_4*g_1^2-939600*g_2*r*e_4^6+166514310*g_2*r*e_4^5*g_1+47190600*g_2*r*e_4^4*g_1^2-8371200*g_2*r*e_4^4+(6032293695/8)*g_2*r*e_4^3*g_1^3-1713960*g_2*r*e_4^3*g_1+231384600*g_2*r*e_4^2*g_1^4-37670400*g_2*r*e_4^2*g_1^2+(340006815/16)*g_2*r*e_4*g_1^5-7712820*g_2*r*e_4*g_1^3-47088000*g_4^3*r*e_4^4-86762100*g_4^3*r*e_4^3*g_1+(2097971685/4)*g_4^3*r*e_4^2*g_1^2+281880*g_4^3*r*e_4^2+(2839579425/16)*g_4^3*r*e_4*g_1^3-26824500*g_4^3*r*e_4*g_1+(1020020445/64)*g_4^3*r*g_1^4-5784615*g_4^3*r*g_1^2-321367500*g_4^2*e_4^5*g_1+(1105849125/2)*g_4^2*e_4^4*g_1^2+37292400*g_4^2*e_4^4+(3133333125/2)*g_4^2*e_4^3*g_1^3-136563390*g_4^2*e_4^3*g_1+(2833390125/32)*g_4^2*e_4^2*g_1^4-314235450*g_4^2*e_4^2*g_1^2+1458000*g_4^2*e_4^2-(776780955/16)*g_4^2*e_4*g_1^3+2142450*g_4^2*e_4*g_1-31392000*g_4*r*e_4^6-56432000*g_4*r*e_4^5*g_1-(82747035/2)*g_4*r*e_4^4*g_1^2+187920*g_4*r*e_4^4-(1702051125/8)*g_4*r*e_4^3*g_1^3-5326200*g_4*r*e_4^3*g_1+(14497565085/32)*g_4*r*e_4^2*g_1^4-439830*g_4*r*e_4^2*g_1^2+(2965507875/16)*g_4*r*e_4*g_1^5-23967900*g_4*r*e_4*g_1^3+(1020020445/64)*g_4*r*g_1^6-5784615*g_4*r*g_1^4-214245000*e_4^7*g_1+221169825*e_4^6*g_1^2+24861600*e_4^6-723076875*e_4^5*g_1^3-56379900*e_4^5*g_1+(16490905425/16)*e_4^4*g_1^4+52358400*e_4^4*g_1^2+972000*e_4^4+(2169230625/2)*e_4^3*g_1^5-(2111684625/8)*e_4^3*g_1^3+285660*e_4^3*g_1+(5100102225/32)*e_4^2*g_1^6-267834600*e_4^2*g_1^4+4374000*e_4^2*g_1^2-(738074025/16)*e_4*g_1^5+1285470*e_4*g_1^3
  L1 = ideal{m1,m2,m3,fac}
  L2 = ideal{m1,m2,m3,facModL}
  
  modPFracGB(L1,{e_4,g_1})
 
  -- huge difference in time in this example!
  time L1gbFrac1 = forceGB gens sub(modPFracGB(L1,{e_4,g_1}),SF)
  time L1gbFrac2 = gb (sub(L1,SF))
  assert(entries gens L1gbFrac1 == entries gens L1gbFrac2)
  -- no discernable difference between fac and fac % L
  time L2gbFrac1 = forceGB gens sub(modPFracGB(L2,{e_4,g_1}),SF)
  time L2gbFrac2 = gb (sub(L2,SF))
  assert(entries gens L2gbFrac1 == entries gens L2gbFrac2)
-------------------

-- Testing factorIrredZeroDimensionalTower
  restart
  debug needsPackage "PD"
  needsPackage "ModularGCD"
  Q = QQ[e_1, e_2, e_3, e_4, g_1, g_2, g_3, g_4, r]
  (S,SF) = makeFiberRings {e_4,g_1}
  use SF
  use coefficientRing SF
  m1 = r^2-3
  m2 = g_4^4+((4*e_4^2+3*g_1^2)/3)*g_4^2+(4*e_4^4+18*e_4^2*g_1^2)/9
  m3 = g_2^2+(9/8)*g_4^2+(2*e_4^2+9*g_1^2)/8
  testList = {m1^2,m2,m3}
  factorTower(testList,"SplitIrred"=>true)
  testList2 = {m1,m2,m3}
  factorTower(testList2,"SplitIrred"=>true)
  f = g_2+(3/(4*e_4*g_1))*g_4^3+((2*e_4^2+3*g_1^2)/(4*e_4*g_1))*g_4
  h = g_2+((-3)/(4*e_4*g_1))*g_4^3+((-2*e_4^2-3*g_1^2)/(4*e_4*g_1))*g_4
  m4 = f^2 % m2
  m4' = f^2*h % m2
  L1 = ideal {m1}
  L2 = ideal {m1,m2}
  -- this is from the stewart-gough platform
  L3 = ideal {m1,m2,m3}
  -- these are slight alterations on this example that could occur
  L4 = ideal {m1,m2,m4}
  L4' = ideal {m1,m2,m4'}
  -- if you run this command enough times, an error occurs in the gbRationalReconstruction code
  -- because G and loopG are different lengths.
  -- I let this run for a long while and it never failed an assert.
  time factorTower L3
  -- change to the last element is a square
  time factorTower(L4,"SplitIrred"=>true)
  -- eliminate is too damn slow, so I wrote quickEliminate that uses the Hilbert hint trick.
  time factorTower L4'
----

--- baby example
restart
  load "gbRatRecon.m2"
  kk = ZZ/32003
  A = kk[g_2, g_3, r, g_1, g_4, MonomialOrder => Lex]
  B = A[x]
  F = x^8+3*x^6*g_1^2+(9/16)*x^4*g_1^4+4*x^6*g_4^2+5*x^4*g_1^2*g_4^2+(3/4)*x^2*g_1^4*g_4^2+(9/2)*x^4*g_4^4+(7/4)*x^2*g_1^2*g_4^4+(1/16)*g_1^4*g_4^4+x^2*g_4^6+(1/8)*g_1^2*g_4^6+(1/16)*g_4^8-9*x^5*g_1^2-12*x^5*g_4^2-24*x^3*g_1^2*g_4^2-(9/4)*x*g_1^4*g_4^2-24*x^3*g_4^4-(21/4)*x*g_1^2*g_4^4-3*x*g_4^6-12*x^6-9*x^4*g_1^2-(27/8)*x^2*g_1^4-12*x^4*g_4^2+54*x^2*g_1^2*g_4^2+(9/4)*g_1^4*g_4^2+57*x^2*g_4^4+(21/4)*g_1^2*g_4^4+3*g_4^6+54*x^3*g_1^2+72*x^3*g_4^2-72*x*g_1^2*g_4^2-72*x*g_4^4+54*x^4-27*x^2*g_1^2+(81/16)*g_1^4-36*x^2*g_4^2+45*g_1^2*g_4^2+(81/2)*g_4^4-81*x*g_1^2-108*x*g_4^2-108*x^2+81*g_1^2+108*g_4^2+81   
  F = sub(F,{x => g_2+g_3+r})
  G = g_2^2-3*g_3^2
  m1 = r^2-3
  m2 = g_3^4+((3*g_1^2+4*g_4^2)/8)*g_3^2+(g_1^2*g_4^2+g_4^4)/16
  L = ideal(F,G,m1,m2)

  -- single parameter
  eval1 = map(A,A,{g_2, g_3, r, g_1, random kk})
  L1 = eval1 L
  gbRationalReconstruction(L1,{g_1})
  
  -- try two parameters
  time gbRationalReconstruction(L,{g_4,g_1})
---------------

-- nastier example over 32003
  restart
  debug needsPackage "PD"
  load "gbRatRecon.m2"
  needsPackage "ModularGCD"
  R = ZZ/32003[e_1, e_2, e_3, e_4, g_1, g_2, g_3, g_4, r]
  (S,SF) = makeFiberRings {e_4,g_1}
  use S
  m1 = r^2-3
  m2 = g_4^4+((4*e_4^2+3*g_1^2)/3)*g_4^2+(4*e_4^4+18*e_4^2*g_1^2)/9
  m3 = g_2^2+(9/8)*g_4^2+(2*e_4^2+9*g_1^2)/8
  F = g_2^8+48*g_2^7*g_4-8*g_2^7*r+1008*g_2^6*g_4^2-336*g_2^6*g_4*r+28*g_2^6*r^2+94*g_2^6*e_4^2-60*g_2^6*e_4*g_1+(297/4)*g_2^6*g_1^2-12*g_2^6+12096*g_2^5*g_4^3-6048*g_2^5*g_4^2*r+1008*g_2^5*g_4*r^2+3384*g_2^5*g_4*e_4^2-2160*g_2^5*g_4*e_4*g_1+2673*g_2^5*g_4*g_1^2-432*g_2^5*g_4-56*g_2^5*r^3-564*g_2^5*r*e_4^2+360*g_2^5*r*e_4*g_1-(891/2)*g_2^5*r*g_1^2+72*g_2^5*r+90720*g_2^4*g_4^4-60480*g_2^4*g_4^3*r+15120*g_2^4*g_4^2*r^2+50760*g_2^4*g_4^2*e_4^2-32400*g_2^4*g_4^2*e_4*g_1+40095*g_2^4*g_4^2*g_1^2-6480*g_2^4*g_4^2-1680*g_2^4*g_4*r^3-16920*g_2^4*g_4*r*e_4^2+10800*g_2^4*g_4*r*e_4*g_1-13365*g_2^4*g_4*r*g_1^2+2160*g_2^4*g_4*r+70*g_2^4*r^4+1410*g_2^4*r^2*e_4^2-900*g_2^4*r^2*e_4*g_1+(4455/4)*g_2^4*r^2*g_1^2-180*g_2^4*r^2+(6819/2)*g_2^4*e_4^4-3114*g_2^4*e_4^3*g_1+9810*g_2^4*e_4^2*g_1^2-282*g_2^4*e_4^2-(7101/2)*g_2^4*e_4*g_1^3+180*g_2^4*e_4*g_1+(93393/64)*g_2^4*g_1^4-(891/4)*g_2^4*g_1^2+54*g_2^4+435456*g_2^3*g_4^5-362880*g_2^3*g_4^4*r+120960*g_2^3*g_4^3*r^2+406080*g_2^3*g_4^3*e_4^2-259200*g_2^3*g_4^3*e_4*g_1+320760*g_2^3*g_4^3*g_1^2-51840*g_2^3*g_4^3-20160*g_2^3*g_4^2*r^3-203040*g_2^3*g_4^2*r*e_4^2+129600*g_2^3*g_4^2*r*e_4*g_1-160380*g_2^3*g_4^2*r*g_1^2+25920*g_2^3*g_4^2*r+1680*g_2^3*g_4*r^4+33840*g_2^3*g_4*r^2*e_4^2-21600*g_2^3*g_4*r^2*e_4*g_1+26730*g_2^3*g_4*r^2*g_1^2-4320*g_2^3*g_4*r^2+81828*g_2^3*g_4*e_4^4-74736*g_2^3*g_4*e_4^3*g_1+235440*g_2^3*g_4*e_4^2*g_1^2-6768*g_2^3*g_4*e_4^2-85212*g_2^3*g_4*e_4*g_1^3+4320*g_2^3*g_4*e_4*g_1+(280179/8)*g_2^3*g_4*g_1^4-5346*g_2^3*g_4*g_1^2+1296*g_2^3*g_4-56*g_2^3*r^5-1880*g_2^3*r^3*e_4^2+1200*g_2^3*r^3*e_4*g_1-1485*g_2^3*r^3*g_1^2+240*g_2^3*r^3-13638*g_2^3*r*e_4^4+12456*g_2^3*r*e_4^3*g_1-39240*g_2^3*r*e_4^2*g_1^2+1128*g_2^3*r*e_4^2+14202*g_2^3*r*e_4*g_1^3-720*g_2^3*r*e_4*g_1-(93393/16)*g_2^3*r*g_1^4+891*g_2^3*r*g_1^2-216*g_2^3*r+1306368*g_2^2*g_4^6-1306368*g_2^2*g_4^5*r+544320*g_2^2*g_4^4*r^2+1827360*g_2^2*g_4^4*e_4^2-1166400*g_2^2*g_4^4*e_4*g_1+1443420*g_2^2*g_4^4*g_1^2-233280*g_2^2*g_4^4-120960*g_2^2*g_4^3*r^3-1218240*g_2^2*g_4^3*r*e_4^2+777600*g_2^2*g_4^3*r*e_4*g_1-962280*g_2^2*g_4^3*r*g_1^2+155520*g_2^2*g_4^3*r+15120*g_2^2*g_4^2*r^4+304560*g_2^2*g_4^2*r^2*e_4^2-194400*g_2^2*g_4^2*r^2*e_4*g_1+240570*g_2^2*g_4^2*r^2*g_1^2-38880*g_2^2*g_4^2*r^2+736452*g_2^2*g_4^2*e_4^4-672624*g_2^2*g_4^2*e_4^3*g_1+2118960*g_2^2*g_4^2*e_4^2*g_1^2-60912*g_2^2*g_4^2*e_4^2-766908*g_2^2*g_4^2*e_4*g_1^3+38880*g_2^2*g_4^2*e_4*g_1+(2521611/8)*g_2^2*g_4^2*g_1^4-48114*g_2^2*g_4^2*g_1^2+11664*g_2^2*g_4^2-1008*g_2^2*g_4*r^5-33840*g_2^2*g_4*r^3*e_4^2+21600*g_2^2*g_4*r^3*e_4*g_1-26730*g_2^2*g_4*r^3*g_1^2+4320*g_2^2*g_4*r^3-245484*g_2^2*g_4*r*e_4^4+224208*g_2^2*g_4*r*e_4^3*g_1-706320*g_2^2*g_4*r*e_4^2*g_1^2+20304*g_2^2*g_4*r*e_4^2+255636*g_2^2*g_4*r*e_4*g_1^3-12960*g_2^2*g_4*r*e_4*g_1-(840537/8)*g_2^2*g_4*r*g_1^4+16038*g_2^2*g_4*r*g_1^2-3888*g_2^2*g_4*r+28*g_2^2*r^6+1410*g_2^2*r^4*e_4^2-900*g_2^2*r^4*e_4*g_1+(4455/4)*g_2^2*r^4*g_1^2-180*g_2^2*r^4+20457*g_2^2*r^2*e_4^4-18684*g_2^2*r^2*e_4^3*g_1+58860*g_2^2*r^2*e_4^2*g_1^2-1692*g_2^2*r^2*e_4^2-21303*g_2^2*r^2*e_4*g_1^3+1080*g_2^2*r^2*e_4*g_1+(280179/32)*g_2^2*r^2*g_1^4-(2673/2)*g_2^2*r^2*g_1^2+324*g_2^2*r^2+(112847/2)*g_2^2*e_4^6-49833*g_2^2*e_4^5*g_1+(4930245/16)*g_2^2*e_4^4*g_1^2+8355*g_2^2*e_4^4-(942813/4)*g_2^2*e_4^3*g_1^3+11628*g_2^2*e_4^3*g_1+(7831161/32)*g_2^2*e_4^2*g_1^4+71226*g_2^2*e_4^2*g_1^2-846*g_2^2*e_4^2-(412371/8)*g_2^2*e_4*g_1^5-10449*g_2^2*e_4*g_1^3+540*g_2^2*e_4*g_1+(24057/8)*g_2^2*g_1^6-(217971/32)*g_2^2*g_1^4-(2673/4)*g_2^2*g_1^2-108*g_2^2+2239488*g_2*g_4^7-2612736*g_2*g_4^6*r+1306368*g_2*g_4^5*r^2+4385664*g_2*g_4^5*e_4^2-2799360*g_2*g_4^5*e_4*g_1+3464208*g_2*g_4^5*g_1^2-559872*g_2*g_4^5-362880*g_2*g_4^4*r^3-3654720*g_2*g_4^4*r*e_4^2+2332800*g_2*g_4^4*r*e_4*g_1-2886840*g_2*g_4^4*r*g_1^2+466560*g_2*g_4^4*r+60480*g_2*g_4^3*r^4+1218240*g_2*g_4^3*r^2*e_4^2-777600*g_2*g_4^3*r^2*e_4*g_1+962280*g_2*g_4^3*r^2*g_1^2-155520*g_2*g_4^3*r^2+2945808*g_2*g_4^3*e_4^4-2690496*g_2*g_4^3*e_4^3*g_1+8475840*g_2*g_4^3*e_4^2*g_1^2-243648*g_2*g_4^3*e_4^2-3067632*g_2*g_4^3*e_4*g_1^3+155520*g_2*g_4^3*e_4*g_1+(2521611/2)*g_2*g_4^3*g_1^4-192456*g_2*g_4^3*g_1^2+46656*g_2*g_4^3-6048*g_2*g_4^2*r^5-203040*g_2*g_4^2*r^3*e_4^2+129600*g_2*g_4^2*r^3*e_4*g_1-160380*g_2*g_4^2*r^3*g_1^2+25920*g_2*g_4^2*r^3-1472904*g_2*g_4^2*r*e_4^4+1345248*g_2*g_4^2*r*e_4^3*g_1-4237920*g_2*g_4^2*r*e_4^2*g_1^2+121824*g_2*g_4^2*r*e_4^2+1533816*g_2*g_4^2*r*e_4*g_1^3-77760*g_2*g_4^2*r*e_4*g_1-(2521611/4)*g_2*g_4^2*r*g_1^4+96228*g_2*g_4^2*r*g_1^2-23328*g_2*g_4^2*r+336*g_2*g_4*r^6+16920*g_2*g_4*r^4*e_4^2-10800*g_2*g_4*r^4*e_4*g_1+13365*g_2*g_4*r^4*g_1^2-2160*g_2*g_4*r^4+245484*g_2*g_4*r^2*e_4^4-224208*g_2*g_4*r^2*e_4^3*g_1+706320*g_2*g_4*r^2*e_4^2*g_1^2-20304*g_2*g_4*r^2*e_4^2-255636*g_2*g_4*r^2*e_4*g_1^3+12960*g_2*g_4*r^2*e_4*g_1+(840537/8)*g_2*g_4*r^2*g_1^4-16038*g_2*g_4*r^2*g_1^2+3888*g_2*g_4*r^2+677082*g_2*g_4*e_4^6-597996*g_2*g_4*e_4^5*g_1+(14790735/4)*g_2*g_4*e_4^4*g_1^2+100260*g_2*g_4*e_4^4-2828439*g_2*g_4*e_4^3*g_1^3+139536*g_2*g_4*e_4^3*g_1+(23493483/8)*g_2*g_4*e_4^2*g_1^4+854712*g_2*g_4*e_4^2*g_1^2-10152*g_2*g_4*e_4^2-(1237113/2)*g_2*g_4*e_4*g_1^5-125388*g_2*g_4*e_4*g_1^3+6480*g_2*g_4*e_4*g_1+(72171/2)*g_2*g_4*g_1^6-(653913/8)*g_2*g_4*g_1^4-8019*g_2*g_4*g_1^2-1296*g_2*g_4-8*g_2*r^7-564*g_2*r^5*e_4^2+360*g_2*r^5*e_4*g_1-(891/2)*g_2*r^5*g_1^2+72*g_2*r^5-13638*g_2*r^3*e_4^4+12456*g_2*r^3*e_4^3*g_1-39240*g_2*r^3*e_4^2*g_1^2+1128*g_2*r^3*e_4^2+14202*g_2*r^3*e_4*g_1^3-720*g_2*r^3*e_4*g_1-(93393/16)*g_2*r^3*g_1^4+891*g_2*r^3*g_1^2-216*g_2*r^3-112847*g_2*r*e_4^6+99666*g_2*r*e_4^5*g_1-(4930245/8)*g_2*r*e_4^4*g_1^2-16710*g_2*r*e_4^4+(942813/2)*g_2*r*e_4^3*g_1^3-23256*g_2*r*e_4^3*g_1-(7831161/16)*g_2*r*e_4^2*g_1^4-142452*g_2*r*e_4^2*g_1^2+1692*g_2*r*e_4^2+(412371/4)*g_2*r*e_4*g_1^5+20898*g_2*r*e_4*g_1^3-1080*g_2*r*e_4*g_1-(24057/4)*g_2*r*g_1^6+(217971/16)*g_2*r*g_1^4+(2673/2)*g_2*r*g_1^2+216*g_2*r+1679616*g_4^8-2239488*g_4^7*r+1306368*g_4^6*r^2+4385664*g_4^6*e_4^2-2799360*g_4^6*e_4*g_1+3464208*g_4^6*g_1^2-559872*g_4^6-435456*g_4^5*r^3-4385664*g_4^5*r*e_4^2+2799360*g_4^5*r*e_4*g_1-3464208*g_4^5*r*g_1^2+559872*g_4^5*r+90720*g_4^4*r^4+1827360*g_4^4*r^2*e_4^2-1166400*g_4^4*r^2*e_4*g_1+1443420*g_4^4*r^2*g_1^2-233280*g_4^4*r^2+4418712*g_4^4*e_4^4-4035744*g_4^4*e_4^3*g_1+12713760*g_4^4*e_4^2*g_1^2-365472*g_4^4*e_4^2-4601448*g_4^4*e_4*g_1^3+233280*g_4^4*e_4*g_1+(7564833/4)*g_4^4*g_1^4-288684*g_4^4*g_1^2+69984*g_4^4-12096*g_4^3*r^5-406080*g_4^3*r^3*e_4^2+259200*g_4^3*r^3*e_4*g_1-320760*g_4^3*r^3*g_1^2+51840*g_4^3*r^3-2945808*g_4^3*r*e_4^4+2690496*g_4^3*r*e_4^3*g_1-8475840*g_4^3*r*e_4^2*g_1^2+243648*g_4^3*r*e_4^2+3067632*g_4^3*r*e_4*g_1^3-155520*g_4^3*r*e_4*g_1-(2521611/2)*g_4^3*r*g_1^4+192456*g_4^3*r*g_1^2-46656*g_4^3*r+1008*g_4^2*r^6+50760*g_4^2*r^4*e_4^2-32400*g_4^2*r^4*e_4*g_1+40095*g_4^2*r^4*g_1^2-6480*g_4^2*r^4+736452*g_4^2*r^2*e_4^4-672624*g_4^2*r^2*e_4^3*g_1+2118960*g_4^2*r^2*e_4^2*g_1^2-60912*g_4^2*r^2*e_4^2-766908*g_4^2*r^2*e_4*g_1^3+38880*g_4^2*r^2*e_4*g_1+(2521611/8)*g_4^2*r^2*g_1^4-48114*g_4^2*r^2*g_1^2+11664*g_4^2*r^2+2031246*g_4^2*e_4^6-1793988*g_4^2*e_4^5*g_1+(44372205/4)*g_4^2*e_4^4*g_1^2+300780*g_4^2*e_4^4-8485317*g_4^2*e_4^3*g_1^3+418608*g_4^2*e_4^3*g_1+(70480449/8)*g_4^2*e_4^2*g_1^4+2564136*g_4^2*e_4^2*g_1^2-30456*g_4^2*e_4^2-(3711339/2)*g_4^2*e_4*g_1^5-376164*g_4^2*e_4*g_1^3+19440*g_4^2*e_4*g_1+(216513/2)*g_4^2*g_1^6-(1961739/8)*g_4^2*g_1^4-24057*g_4^2*g_1^2-3888*g_4^2-48*g_4*r^7-3384*g_4*r^5*e_4^2+2160*g_4*r^5*e_4*g_1-2673*g_4*r^5*g_1^2+432*g_4*r^5-81828*g_4*r^3*e_4^4+74736*g_4*r^3*e_4^3*g_1-235440*g_4*r^3*e_4^2*g_1^2+6768*g_4*r^3*e_4^2+85212*g_4*r^3*e_4*g_1^3-4320*g_4*r^3*e_4*g_1-(280179/8)*g_4*r^3*g_1^4+5346*g_4*r^3*g_1^2-1296*g_4*r^3-677082*g_4*r*e_4^6+597996*g_4*r*e_4^5*g_1-(14790735/4)*g_4*r*e_4^4*g_1^2-100260*g_4*r*e_4^4+2828439*g_4*r*e_4^3*g_1^3-139536*g_4*r*e_4^3*g_1-(23493483/8)*g_4*r*e_4^2*g_1^4-854712*g_4*r*e_4^2*g_1^2+10152*g_4*r*e_4^2+(1237113/2)*g_4*r*e_4*g_1^5+125388*g_4*r*e_4*g_1^3-6480*g_4*r*e_4*g_1-(72171/2)*g_4*r*g_1^6+(653913/8)*g_4*r*g_1^4+8019*g_4*r*g_1^2+1296*g_4*r+r^8+94*r^6*e_4^2-60*r^6*e_4*g_1+(297/4)*r^6*g_1^2-12*r^6+(6819/2)*r^4*e_4^4-3114*r^4*e_4^3*g_1+9810*r^4*e_4^2*g_1^2-282*r^4*e_4^2-(7101/2)*r^4*e_4*g_1^3+180*r^4*e_4*g_1+(93393/64)*r^4*g_1^4-(891/4)*r^4*g_1^2+54*r^4+(112847/2)*r^2*e_4^6-49833*r^2*e_4^5*g_1+(4930245/16)*r^2*e_4^4*g_1^2+8355*r^2*e_4^4-(942813/4)*r^2*e_4^3*g_1^3+11628*r^2*e_4^3*g_1+(7831161/32)*r^2*e_4^2*g_1^4+71226*r^2*e_4^2*g_1^2-846*r^2*e_4^2-(412371/8)*r^2*e_4*g_1^5-10449*r^2*e_4*g_1^3+540*r^2*e_4*g_1+(24057/8)*r^2*g_1^6-(217971/32)*r^2*g_1^4-(2673/4)*r^2*g_1^2-108*r^2+(5764801/16)*e_4^8-(352947/2)*e_4^7*g_1+(52401825/16)*e_4^6*g_1^2+(338541/2)*e_4^6-(3181815/2)*e_4^5*g_1^3-149499*e_4^5*g_1+(485624241/64)*e_4^4*g_1^4+(14790735/16)*e_4^4*g_1^2+(61371/2)*e_4^4-(28779219/8)*e_4^3*g_1^5-(2828439/4)*e_4^3*g_1^3-28026*e_4^3*g_1+(5256819/8)*e_4^2*g_1^6+(23493483/32)*e_4^2*g_1^4+88290*e_4^2*g_1^2+2538*e_4^2-(107163/2)*e_4*g_1^7-(1237113/8)*e_4*g_1^5-(63909/2)*e_4*g_1^3-1620*e_4*g_1+(6561/4)*g_1^8+(72171/8)*g_1^6+(840537/64)*g_1^4+(8019/4)*g_1^2+81
  L = ideal{m1,m2,m3,F}
  -- note the time difference!
  LratRecon = time first gbRationalReconstruction(L,{e_4,g_1})
  time LSF = gens gb (sub(L,SF))
  assert (ideal LSF == sub(ideal LratRecon,SF))
  assert (numerator LSF_2_0 == LratRecon_2)
  
  RZ = ZZ(monoid R)
  netList for i from 0 to #LratRecon - 1 list integerRationalReconstruction(sub(LratRecon_i,RZ), 32003)
  
  -- getting the 'other' factor via division
  m3SF = sub(m3,SF)
  newFac = sub(last LratRecon, SF)
  newFac = (1/leadCoefficient newFac)*newFac
  m3SF // newFac

-- same example above, but over QQ
  restart
  debug needsPackage "PD"
  load "gbRatRecon.m2"
  needsPackage "ModularGCD"
  Q = QQ[e_1, e_2, e_3, e_4, g_1, g_2, g_3, g_4, r]
  (S,SF) = makeFiberRings {e_4,g_1}
  use S
  m1 = r^2-3
  m2 = g_4^4+((4*e_4^2+3*g_1^2)/3)*g_4^2+(4*e_4^4+18*e_4^2*g_1^2)/9
  m3 = g_2^2+(9/8)*g_4^2+(2*e_4^2+9*g_1^2)/8
  fac = 43046721*g_2^8+191318760*g_2^7*g_4-38263752*g_2^7*r+372008700*g_2^6*g_4^2-148803480*g_2^6*g_4*r+14880348*g_2^6*r^2-50664042*g_2^6*e_4^2-239148450*g_2^6*e_4*g_1+(493708689/4)*g_2^6*g_1^2-6377292*g_2^6+413343000*g_2^5*g_4^3-248005800*g_2^5*g_4^2*r+49601160*g_2^5*g_4*r^2-168880140*g_2^5*g_4*e_4^2-797161500*g_2^5*g_4*e_4*g_1+(822847815/2)*g_2^5*g_4*g_1^2-21257640*g_2^5*g_4-3306744*g_2^5*r^3+33776028*g_2^5*r*e_4^2+159432300*g_2^5*r*e_4*g_1-(164569563/2)*g_2^5*r*g_1^2+4251528*g_2^5*r+287043750*g_2^4*g_4^4-229635000*g_2^4*g_4^3*r+68890500*g_2^4*g_4^2*r^2-234555750*g_2^4*g_4^2*e_4^2-1107168750*g_2^4*g_4^2*e_4*g_1+(2285688375/4)*g_2^4*g_4^2*g_1^2-29524500*g_2^4*g_4^2-9185400*g_2^4*g_4*r^3+93822300*g_2^4*g_4*r*e_4^2+442867500*g_2^4*g_4*r*e_4*g_1-(457137675/2)*g_2^4*g_4*r*g_1^2+11809800*g_2^4*g_4*r+459270*g_2^4*r^4-9382230*g_2^4*r^2*e_4^2-44286750*g_2^4*r^2*e_4*g_1+(91427535/4)*g_2^4*r^2*g_1^2-1180980*g_2^4*r^2+(115580763/2)*g_2^4*e_4^4+106977105*g_2^4*e_4^3*g_1+(918266625/2)*g_2^4*e_4^2*g_1^2+1876446*g_2^4*e_4^2-(1979027235/4)*g_2^4*e_4*g_1^3+8857350*g_2^4*e_4*g_1+(7575599601/64)*g_2^4*g_1^4-(18285507/4)*g_2^4*g_1^2+354294*g_2^4+127575000*g_2^3*g_4^5-127575000*g_2^3*g_4^4*r+51030000*g_2^3*g_4^3*r^2-173745000*g_2^3*g_4^3*e_4^2-820125000*g_2^3*g_4^3*e_4*g_1+423275625*g_2^3*g_4^3*g_1^2-21870000*g_2^3*g_4^3-10206000*g_2^3*g_4^2*r^3+104247000*g_2^3*g_4^2*r*e_4^2+492075000*g_2^3*g_4^2*r*e_4*g_1-253965375*g_2^3*g_4^2*r*g_1^2+13122000*g_2^3*g_4^2*r+1020600*g_2^3*g_4*r^4-20849400*g_2^3*g_4*r^2*e_4^2-98415000*g_2^3*g_4*r^2*e_4*g_1+50793075*g_2^3*g_4*r^2*g_1^2-2624400*g_2^3*g_4*r^2+128423070*g_2^3*g_4*e_4^4+237726900*g_2^3*g_4*e_4^3*g_1+1020296250*g_2^3*g_4*e_4^2*g_1^2+4169880*g_2^3*g_4*e_4^2-1099459575*g_2^3*g_4*e_4*g_1^3+19683000*g_2^3*g_4*e_4*g_1+(4208666445/16)*g_2^3*g_4*g_1^4-10158615*g_2^3*g_4*g_1^2+787320*g_2^3*g_4-40824*g_2^3*r^5+1389960*g_2^3*r^3*e_4^2+6561000*g_2^3*r^3*e_4*g_1-3386205*g_2^3*r^3*g_1^2+174960*g_2^3*r^3-25684614*g_2^3*r*e_4^4-47545380*g_2^3*r*e_4^3*g_1-204059250*g_2^3*r*e_4^2*g_1^2-833976*g_2^3*r*e_4^2+219891915*g_2^3*r*e_4*g_1^3-3936600*g_2^3*r*e_4*g_1-(841733289/16)*g_2^3*r*g_1^4+2031723*g_2^3*r*g_1^2-157464*g_2^3*r+35437500*g_2^2*g_4^6-42525000*g_2^2*g_4^5*r+21262500*g_2^2*g_4^4*r^2-72393750*g_2^2*g_4^4*e_4^2-341718750*g_2^2*g_4^4*e_4*g_1+(705459375/4)*g_2^2*g_4^4*g_1^2-9112500*g_2^2*g_4^4-5670000*g_2^2*g_4^3*r^3+57915000*g_2^2*g_4^3*r*e_4^2+273375000*g_2^2*g_4^3*r*e_4*g_1-141091875*g_2^2*g_4^3*r*g_1^2+7290000*g_2^2*g_4^3*r+850500*g_2^2*g_4^2*r^4-17374500*g_2^2*g_4^2*r^2*e_4^2-82012500*g_2^2*g_4^2*r^2*e_4*g_1+(84655125/2)*g_2^2*g_4^2*r^2*g_1^2-2187000*g_2^2*g_4^2*r^2+107019225*g_2^2*g_4^2*e_4^4+198105750*g_2^2*g_4^2*e_4^3*g_1+850246875*g_2^2*g_4^2*e_4^2*g_1^2+3474900*g_2^2*g_4^2*e_4^2-(1832432625/2)*g_2^2*g_4^2*e_4*g_1^3+16402500*g_2^2*g_4^2*e_4*g_1+(7014444075/32)*g_2^2*g_4^2*g_1^4-(16931025/2)*g_2^2*g_4^2*g_1^2+656100*g_2^2*g_4^2-68040*g_2^2*g_4*r^5+2316600*g_2^2*g_4*r^3*e_4^2+10935000*g_2^2*g_4*r^3*e_4*g_1-5643675*g_2^2*g_4*r^3*g_1^2+291600*g_2^2*g_4*r^3-42807690*g_2^2*g_4*r*e_4^4-79242300*g_2^2*g_4*r*e_4^3*g_1-340098750*g_2^2*g_4*r*e_4^2*g_1^2-1389960*g_2^2*g_4*r*e_4^2+366486525*g_2^2*g_4*r*e_4*g_1^3-6561000*g_2^2*g_4*r*e_4*g_1-(1402888815/16)*g_2^2*g_4*r*g_1^4+3386205*g_2^2*g_4*r*g_1^2-262440*g_2^2*g_4*r+2268*g_2^2*r^6-115830*g_2^2*r^4*e_4^2-546750*g_2^2*r^4*e_4*g_1+(1128735/4)*g_2^2*r^4*g_1^2-14580*g_2^2*r^4+4280769*g_2^2*r^2*e_4^4+7924230*g_2^2*r^2*e_4^3*g_1+34009875*g_2^2*r^2*e_4^2*g_1^2+138996*g_2^2*r^2*e_4^2-(73297305/2)*g_2^2*r^2*e_4*g_1^3+656100*g_2^2*r^2*e_4*g_1+(280577763/32)*g_2^2*r^2*g_1^4-(677241/2)*g_2^2*r^2*g_1^2+26244*g_2^2*r^2-(50471421/2)*g_2^2*e_4^6-(198509535/2)*g_2^2*e_4^5*g_1+(604425933/16)*g_2^2*e_4^4*g_1^2+8425323*g_2^2*e_4^4-(4107950235/8)*g_2^2*e_4^3*g_1^3-17926110*g_2^2*e_4^3*g_1+(22097332251/32)*g_2^2*e_4^2*g_1^4+25135839*g_2^2*e_4^2*g_1^2+69498*g_2^2*e_4^2-(4813007445/16)*g_2^2*e_4*g_1^5-(16719615/2)*g_2^2*e_4*g_1^3+328050*g_2^2*e_4*g_1+(1371413025/32)*g_2^2*g_1^6+(2857437/32)*g_2^2*g_1^4-(677241/4)*g_2^2*g_1^2-8748*g_2^2+5625000*g_2*g_4^7-7875000*g_2*g_4^6*r+4725000*g_2*g_4^5*r^2-16087500*g_2*g_4^5*e_4^2-75937500*g_2*g_4^5*e_4*g_1+(78384375/2)*g_2*g_4^5*g_1^2-2025000*g_2*g_4^5-1575000*g_2*g_4^4*r^3+16087500*g_2*g_4^4*r*e_4^2+75937500*g_2*g_4^4*r*e_4*g_1-(78384375/2)*g_2*g_4^4*r*g_1^2+2025000*g_2*g_4^4*r+315000*g_2*g_4^3*r^4-6435000*g_2*g_4^3*r^2*e_4^2-30375000*g_2*g_4^3*r^2*e_4*g_1+15676875*g_2*g_4^3*r^2*g_1^2-810000*g_2*g_4^3*r^2+39636750*g_2*g_4^3*e_4^4+73372500*g_2*g_4^3*e_4^3*g_1+314906250*g_2*g_4^3*e_4^2*g_1^2+1287000*g_2*g_4^3*e_4^2-339339375*g_2*g_4^3*e_4*g_1^3+6075000*g_2*g_4^3*e_4*g_1+(1298971125/16)*g_2*g_4^3*g_1^4-3135375*g_2*g_4^3*g_1^2+243000*g_2*g_4^3-37800*g_2*g_4^2*r^5+1287000*g_2*g_4^2*r^3*e_4^2+6075000*g_2*g_4^2*r^3*e_4*g_1-3135375*g_2*g_4^2*r^3*g_1^2+162000*g_2*g_4^2*r^3-23782050*g_2*g_4^2*r*e_4^4-44023500*g_2*g_4^2*r*e_4^3*g_1-188943750*g_2*g_4^2*r*e_4^2*g_1^2-772200*g_2*g_4^2*r*e_4^2+203603625*g_2*g_4^2*r*e_4*g_1^3-3645000*g_2*g_4^2*r*e_4*g_1-(779382675/16)*g_2*g_4^2*r*g_1^4+1881225*g_2*g_4^2*r*g_1^2-145800*g_2*g_4^2*r+2520*g_2*g_4*r^6-128700*g_2*g_4*r^4*e_4^2-607500*g_2*g_4*r^4*e_4*g_1+(627075/2)*g_2*g_4*r^4*g_1^2-16200*g_2*g_4*r^4+4756410*g_2*g_4*r^2*e_4^4+8804700*g_2*g_4*r^2*e_4^3*g_1+37788750*g_2*g_4*r^2*e_4^2*g_1^2+154440*g_2*g_4*r^2*e_4^2-40720725*g_2*g_4*r^2*e_4*g_1^3+729000*g_2*g_4*r^2*e_4*g_1+(155876535/16)*g_2*g_4*r^2*g_1^4-376245*g_2*g_4*r^2*g_1^2+29160*g_2*g_4*r^2-(84119035/3)*g_2*g_4*e_4^6-110283075*g_2*g_4*e_4^5*g_1+(335792185/8)*g_2*g_4*e_4^4*g_1^2+9361470*g_2*g_4*e_4^4-(2282194575/4)*g_2*g_4*e_4^3*g_1^3-19917900*g_2*g_4*e_4^3*g_1+(12276295695/16)*g_2*g_4*e_4^2*g_1^4+27928710*g_2*g_4*e_4^2*g_1^2+77220*g_2*g_4*e_4^2-(2673893025/8)*g_2*g_4*e_4*g_1^5-9288675*g_2*g_4*e_4*g_1^3+364500*g_2*g_4*e_4*g_1+(761896125/16)*g_2*g_4*g_1^6+(1587465/16)*g_2*g_4*g_1^4-(376245/2)*g_2*g_4*g_1^2-9720*g_2*g_4-72*g_2*r^7+5148*g_2*r^5*e_4^2+24300*g_2*r^5*e_4*g_1-(25083/2)*g_2*r^5*g_1^2+648*g_2*r^5-317094*g_2*r^3*e_4^4-586980*g_2*r^3*e_4^3*g_1-2519250*g_2*r^3*e_4^2*g_1^2-10296*g_2*r^3*e_4^2+2714715*g_2*r^3*e_4*g_1^3-48600*g_2*r^3*e_4*g_1-(10391769/16)*g_2*r^3*g_1^4+25083*g_2*r^3*g_1^2-1944*g_2*r^3+(16823807/3)*g_2*r*e_4^6+22056615*g_2*r*e_4^5*g_1-(67158437/8)*g_2*r*e_4^4*g_1^2-1872294*g_2*r*e_4^4+(456438915/4)*g_2*r*e_4^3*g_1^3+3983580*g_2*r*e_4^3*g_1-(2455259139/16)*g_2*r*e_4^2*g_1^4-5585742*g_2*r*e_4^2*g_1^2-15444*g_2*r*e_4^2+(534778605/8)*g_2*r*e_4*g_1^5+1857735*g_2*r*e_4*g_1^3-72900*g_2*r*e_4*g_1-(152379225/16)*g_2*r*g_1^6-(317493/16)*g_2*r*g_1^4+(75249/2)*g_2*r*g_1^2+1944*g_2*r+390625*g_4^8-625000*g_4^7*r+437500*g_4^6*r^2-(4468750/3)*g_4^6*e_4^2-7031250*g_4^6*e_4*g_1+(14515625/4)*g_4^6*g_1^2-187500*g_4^6-175000*g_4^5*r^3+1787500*g_4^5*r*e_4^2+8437500*g_4^5*r*e_4*g_1-(8709375/2)*g_4^5*r*g_1^2+225000*g_4^5*r+43750*g_4^4*r^4-893750*g_4^4*r^2*e_4^2-4218750*g_4^4*r^2*e_4*g_1+(8709375/4)*g_4^4*r^2*g_1^2-112500*g_4^4*r^2+(33030625/6)*g_4^4*e_4^4+10190625*g_4^4*e_4^3*g_1+(262421875/6)*g_4^4*e_4^2*g_1^2+178750*g_4^4*e_4^2-(188521875/4)*g_4^4*e_4*g_1^3+843750*g_4^4*e_4*g_1+(721650625/64)*g_4^4*g_1^4-(1741875/4)*g_4^4*g_1^2+33750*g_4^4-7000*g_4^3*r^5+(715000/3)*g_4^3*r^3*e_4^2+1125000*g_4^3*r^3*e_4*g_1-580625*g_4^3*r^3*g_1^2+30000*g_4^3*r^3-(13212250/3)*g_4^3*r*e_4^4-8152500*g_4^3*r*e_4^3*g_1-(104968750/3)*g_4^3*r*e_4^2*g_1^2-143000*g_4^3*r*e_4^2+37704375*g_4^3*r*e_4*g_1^3-675000*g_4^3*r*e_4*g_1-(144330125/16)*g_4^3*r*g_1^4+348375*g_4^3*r*g_1^2-27000*g_4^3*r+700*g_4^2*r^6-35750*g_4^2*r^4*e_4^2-168750*g_4^2*r^4*e_4*g_1+(348375/4)*g_4^2*r^4*g_1^2-4500*g_4^2*r^4+1321225*g_4^2*r^2*e_4^4+2445750*g_4^2*r^2*e_4^3*g_1+10496875*g_4^2*r^2*e_4^2*g_1^2+42900*g_4^2*r^2*e_4^2-(22622625/2)*g_4^2*r^2*e_4*g_1^3+202500*g_4^2*r^2*e_4*g_1+(86598075/32)*g_4^2*r^2*g_1^4-(209025/2)*g_4^2*r^2*g_1^2+8100*g_4^2*r^2-(420595175/54)*g_4^2*e_4^6-(61268375/2)*g_4^2*e_4^5*g_1+(1678960925/144)*g_4^2*e_4^4*g_1^2+(7801225/3)*g_4^2*e_4^4-(1267885875/8)*g_4^2*e_4^3*g_1^3-5532750*g_4^2*e_4^3*g_1+(6820164275/32)*g_4^2*e_4^2*g_1^4+7757975*g_4^2*e_4^2*g_1^2+21450*g_4^2*e_4^2-(1485496125/16)*g_4^2*e_4*g_1^5-(5160375/2)*g_4^2*e_4*g_1^3+101250*g_4^2*e_4*g_1+(423275625/32)*g_4^2*g_1^6+(881925/32)*g_4^2*g_1^4-(209025/4)*g_4^2*g_1^2-2700*g_4^2-40*g_4*r^7+2860*g_4*r^5*e_4^2+13500*g_4*r^5*e_4*g_1-(13935/2)*g_4*r^5*g_1^2+360*g_4*r^5-(528490/3)*g_4*r^3*e_4^4-326100*g_4*r^3*e_4^3*g_1-(4198750/3)*g_4*r^3*e_4^2*g_1^2-5720*g_4*r^3*e_4^2+1508175*g_4*r^3*e_4*g_1^3-27000*g_4*r^3*e_4*g_1-(5773205/16)*g_4*r^3*g_1^4+13935*g_4*r^3*g_1^2-1080*g_4*r^3+(84119035/27)*g_4*r*e_4^6+12253675*g_4*r*e_4^5*g_1-(335792185/72)*g_4*r*e_4^4*g_1^2-(3120490/3)*g_4*r*e_4^4+(253577175/4)*g_4*r*e_4^3*g_1^3+2213100*g_4*r*e_4^3*g_1-(1364032855/16)*g_4*r*e_4^2*g_1^4-3103190*g_4*r*e_4^2*g_1^2-8580*g_4*r*e_4^2+(297099225/8)*g_4*r*e_4*g_1^5+1032075*g_4*r*e_4*g_1^3-40500*g_4*r*e_4*g_1-(84655125/16)*g_4*r*g_1^6-(176385/16)*g_4*r*g_1^4+(41805/2)*g_4*r*g_1^2+1080*g_4*r+r^8-(286/3)*r^6*e_4^2-450*r^6*e_4*g_1+(929/4)*r^6*g_1^2-12*r^6+(52849/6)*r^4*e_4^4+16305*r^4*e_4^3*g_1+(419875/6)*r^4*e_4^2*g_1^2+286*r^4*e_4^2-(301635/4)*r^4*e_4*g_1^3+1350*r^4*e_4*g_1+(1154641/64)*r^4*g_1^4-(2787/4)*r^4*g_1^2+54*r^4-(16823807/54)*r^2*e_4^6-(2450735/2)*r^2*e_4^5*g_1+(67158437/144)*r^2*e_4^4*g_1^2+(312049/3)*r^2*e_4^4-(50715435/8)*r^2*e_4^3*g_1^3-221310*r^2*e_4^3*g_1+(272806571/32)*r^2*e_4^2*g_1^4+310319*r^2*e_4^2*g_1^2+858*r^2*e_4^2-(59419845/16)*r^2*e_4*g_1^5-(206415/2)*r^2*e_4*g_1^3+4050*r^2*e_4*g_1+(16931025/32)*r^2*g_1^6+(35277/32)*r^2*g_1^4-(8361/4)*r^2*g_1^2-108*r^2+(13841287201/1296)*e_4^8-(201768035/12)*e_4^7*g_1+(15270722551/144)*e_4^6*g_1^2-(16823807/18)*e_4^6-(307861365/2)*e_4^5*g_1^3-(7352205/2)*e_4^5*g_1+(19575431101/64)*e_4^4*g_1^4+(67158437/48)*e_4^4*g_1^2+(158547/2)*e_4^4-(5822807445/16)*e_4^3*g_1^5-(152146305/8)*e_4^3*g_1^3+146745*e_4^3*g_1+(6506270325/32)*e_4^2*g_1^6+(818419713/32)*e_4^2*g_1^4+(1259625/2)*e_4^2*g_1^2-2574*e_4^2-(843908625/16)*e_4*g_1^7-(178259535/16)*e_4*g_1^5-(2714715/4)*e_4*g_1^3-12150*e_4*g_1+(332150625/64)*g_1^8+(50793075/32)*g_1^6+(10391769/64)*g_1^4+(25083/4)*g_1^2+81
  facModL = -221169825*g_2*g_4^3*e_4^3*g_1-1205128125*g_2*g_4^3*e_4^2*g_1^2+51993540*g_2*g_4^3*e_4^2-(566678025/16)*g_2*g_4^3*e_4*g_1^3+224957250*g_2*g_4^3*e_4*g_1+(66344535/2)*g_2*g_4^3*g_1^2-1713960*g_2*g_4^3-1409400*g_2*g_4^2*r*e_4^4+343947465*g_2*g_4^2*r*e_4^3*g_1+244310100*g_2*g_4^2*r*e_4^2*g_1^2-12556800*g_2*g_4^2*r*e_4^2+(1313107605/16)*g_2*g_4^2*r*e_4*g_1^3-3134700*g_2*g_4^2*r*e_4*g_1-(62964225/8)*g_2*g_4^2*r*g_1^4-2856600*g_2*g_4^2*r*g_1^2-147446550*g_2*g_4*e_4^5*g_1-160683750*g_2*g_4*e_4^4*g_1^2+34662360*g_2*g_4*e_4^4-(5496968475/8)*g_2*g_4*e_4^3*g_1^3+75386700*g_2*g_4*e_4^3*g_1-723076875*g_2*g_4*e_4^2*g_1^4+191254545*g_2*g_4*e_4^2*g_1^2-1142640*g_2*g_4*e_4^2-(1700034075/16)*g_2*g_4*e_4*g_1^5+178556400*g_2*g_4*e_4*g_1^3-2916000*g_2*g_4*e_4*g_1+(246024675/8)*g_2*g_4*g_1^4-856980*g_2*g_4*g_1^2-939600*g_2*r*e_4^6+166514310*g_2*r*e_4^5*g_1+47190600*g_2*r*e_4^4*g_1^2-8371200*g_2*r*e_4^4+(6032293695/8)*g_2*r*e_4^3*g_1^3-1713960*g_2*r*e_4^3*g_1+231384600*g_2*r*e_4^2*g_1^4-37670400*g_2*r*e_4^2*g_1^2+(340006815/16)*g_2*r*e_4*g_1^5-7712820*g_2*r*e_4*g_1^3-47088000*g_4^3*r*e_4^4-86762100*g_4^3*r*e_4^3*g_1+(2097971685/4)*g_4^3*r*e_4^2*g_1^2+281880*g_4^3*r*e_4^2+(2839579425/16)*g_4^3*r*e_4*g_1^3-26824500*g_4^3*r*e_4*g_1+(1020020445/64)*g_4^3*r*g_1^4-5784615*g_4^3*r*g_1^2-321367500*g_4^2*e_4^5*g_1+(1105849125/2)*g_4^2*e_4^4*g_1^2+37292400*g_4^2*e_4^4+(3133333125/2)*g_4^2*e_4^3*g_1^3-136563390*g_4^2*e_4^3*g_1+(2833390125/32)*g_4^2*e_4^2*g_1^4-314235450*g_4^2*e_4^2*g_1^2+1458000*g_4^2*e_4^2-(776780955/16)*g_4^2*e_4*g_1^3+2142450*g_4^2*e_4*g_1-31392000*g_4*r*e_4^6-56432000*g_4*r*e_4^5*g_1-(82747035/2)*g_4*r*e_4^4*g_1^2+187920*g_4*r*e_4^4-(1702051125/8)*g_4*r*e_4^3*g_1^3-5326200*g_4*r*e_4^3*g_1+(14497565085/32)*g_4*r*e_4^2*g_1^4-439830*g_4*r*e_4^2*g_1^2+(2965507875/16)*g_4*r*e_4*g_1^5-23967900*g_4*r*e_4*g_1^3+(1020020445/64)*g_4*r*g_1^6-5784615*g_4*r*g_1^4-214245000*e_4^7*g_1+221169825*e_4^6*g_1^2+24861600*e_4^6-723076875*e_4^5*g_1^3-56379900*e_4^5*g_1+(16490905425/16)*e_4^4*g_1^4+52358400*e_4^4*g_1^2+972000*e_4^4+(2169230625/2)*e_4^3*g_1^5-(2111684625/8)*e_4^3*g_1^3+285660*e_4^3*g_1+(5100102225/32)*e_4^2*g_1^6-267834600*e_4^2*g_1^4+4374000*e_4^2*g_1^2-(738074025/16)*e_4*g_1^5+1285470*e_4*g_1^3
  L1 = ideal{m1,m2,m3,fac}
  L2 = ideal{m1,m2,m3,facModL}
  
-- rat recon over 32003
  SZ = ZZ(monoid S)
  Sp = (ZZ/32003)(monoid S)
  L1p = sub(L1,Sp)
  L1pratRecon = time ideal first gbRationalReconstruction(L1p,apply({e_4,g_1},x -> sub(x,Sp)))
  L1pratReconQ = time integerRationalReconstruction(sub(L1pratRecon,SZ),32003)
  
-- now different prime, 32009
  Sq = (ZZ/32009)(monoid S)
  L1q = sub(L1,Sq)
  L1qratRecon = time ideal first gbRationalReconstruction(L1q,apply({e_4,g_1},x -> sub(x,Sq)))
  L1qratReconQ = integerRationalReconstruction(sub(L1qratRecon,SZ),32009)
-- same answer?  then we are done.
  L1qratReconQ_* == L1pratReconQ_*
---------------

--- bigger example
restart
load "gbRatRecon.m2"
load "PD.m2"
debug PD
R = ZZ/32003[a,b,c,d,e,f,g,h,j,k,l, MonomialOrder=>Lex]
I = ideal(h*j*l-2*e*g+16001*c*j+16001*a*l,h*j*k-2*e*f+16001*b*j+16001*a*k,h*j^2+2*e^2+16001*a*j,d*j^2+2*a*e,g*h*j+e*h*l+8001*d*j*l+16001*c*e+16001*a*g,f*h*j+e*h*k+8001*d*j*k+16001*b*e+16001*a*f
          ,e*g*j+8001*c*j^2+e^2*l,d*g*j+d*e*l+16001*a*c,e*f*j+8001*b*j^2+e^2*k,d*f*j+d*e*k+16001*a*b,d*e*j-a*h*j-16001*a^2,d*e^2-a*e*h-8001*a*d*j,d*g*k*l-c*h*k*l-d*f*l^2+b*h*l^2-2*c*f*g+2*b*g^2-16001
       	  *c^2*k+16001*b*c*l,d*g*k^2-c*h*k^2-d*f*k*l+b*h*k*l-2*c*f^2+2*b*f*g-16001*b*c*k+16001*b^2*l,d*g^2*k-c*g*h*k-d*f*g*l+c*f*h*l-8001*c*d*k*l+8001*b*d*l^2+16001*c^2*f-16001*b*c*g,d*f*g*k-b*g*h*k-
       	  8001*c*d*k^2-d*f^2*l+b*f*h*l+8001*b*d*k*l+16001*b*c*f-16001*b^2*g,c*f*g*k-b*g^2*k-8001*c^2*k^2-c*f^2*l+b*f*g*l-16001*b*c*k*l-8001*b^2*l^2,e^2*g*k+8001*c*e*j*k-e^2*f*l-8001*b*e*j*l,d*g*h*l^2
       	  -c*h^2*l^2-8001*d^2*l^3+2*d*g^3-2*c*g^2*h+16000*c*d*g*l+c^2*h*l-8001*c^3,d*f*h*l^2-b*h^2*l^2-8001*d^2*k*l^2+2*d*f*g^2-2*b*g^2*h+16001*c*d*g*k+16001*c*d*f*l+16001*b*d*g*l+b*c*h*l-8001*b*c^2,
       	  d*f*h*k*l-b*h^2*k*l-8001*d^2*k^2*l+2*d*f^2*g-2*b*f*g*h+16001*c*d*f*k+16001*b*d*g*k-16001*b*c*h*k+16001*b*d*f*l-16001*b^2*h*l-8001*b^2*c,d*f*h*k^2-b*h^2*k^2-8001*d^2*k^3+2*d*f^3-2*b*f^2*h+
       	  16000*b*d*f*k+b^2*h*k-8001*b^3)
see I
independentSet = support first independentSets(I, Limit=>1)
time gbRationalReconstruction(I,independentSet)

-- cut down on some variables
S = ZZ/32003[a,b,c,g,h,j,k,l,MonomialOrder=>Lex]
phi = map(S,R,matrix{{a,b,c,random kk, random kk, random kk, g,h,j,k,l}})
see phi I
independentSet = support first independentSets phi I
time first gbRationalReconstruction(phi I, independentSet)

-- see what the gb over fraction field is
(RU,KR) = makeFiberRings(independentSet)
IKR = sub(phi I, KR)
netList flatten entries gens gb IKR
-- works!
  
-- cut down on fewer variables
S = ZZ/32003[a,b,c,d,g,h,j,k,l,MonomialOrder=>Lex]
phi = map(S,R,matrix{{a,b,c,d, random kk, random kk, g,h,j,k,l}})
independentSet = support first independentSets phi I
time ratGB = gbRationalReconstruction(phi I, independentSet)

-- see what the gb over fraction field is
(RU,KR) = makeFiberRings(independentSet)
IKR = sub(phi I, KR)
netList flatten entries gens gb IKR
-- works (note: with denominators)!

-- with many variables in the independent set, the number of evaluations grow exponentially...

-- cut down on still fewer variables
S = ZZ/32003[a,b,c,d,e,g,h,j,k,l,MonomialOrder=>Lex]
phi = map(S,R,matrix{{a,b,c,d,e, random kk, g,h,j,k,l}})
independentSet = support first independentSets phi I
time ratGB = gbRationalReconstruction(phi I, independentSet)

-- see what the gb over fraction field is
(RU,KR) = makeFiberRings(independentSet)
IKR = sub(phi I, KR)
netList flatten entries gens gb IKR
-- works!

--- another exmaple from PD.m2
restart
load "gbRatRecon.m2"
load "PD.m2"
debug PD
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
  (J,psi) = simplifyIdeal I
independentSet = support first independentSets J
(RU,KR) = makeFiberRings(independentSet)
IKR = sub(J, KR)
-- long time
netList flatten entries gens gb IKR
-- try new thing?
gbRationalReconstruction(J,independentSet)

-- cut down on all but one variables
S = ZZ/32003[a,b,c,d,f,g,s,t,w,x,y,z,MonomialOrder=>Lex]
phi = map(S,R,matrix{{a,b,c,d,f,g,random kk,random kk,random kk,s,t,random kk,random kk,w,x,y,z}})
see phi J
independentSet = support first independentSets(phi J, Limit=>1)
gbTrace = 3
time first gbRationalReconstruction(phi J, independentSet)
-- check
(RU,KR) = makeFiberRings(independentSet)
describe KR
JKR = sub(phi J, KR)
see JKR
gbTrace = 3
time netList flatten entries gens gb JKR

-- cut down on all but one variable
S = ZZ/32003[a,b,c,d,f,g,h,s,t,w,x,y,z,MonomialOrder=>Lex]
phi = map(S,R,matrix{{a,b,c,d,f,g,h,random kk,random kk,s,t,random kk,random kk,w,x,y,z}})
see phi J
independentSet = support first independentSets(phi J, Limit=>1)
gbTrace = 3
use S
time first gbRationalReconstruction(phi J, {h,w,y,z})
-- check
(RU,KR) = makeFiberRings({h,w,y,z})
describe KR
JKR = sub(phi J, KR)
see JKR
gbTrace = 3
time netList flatten entries gens gb JKR

-- cut down on all but two variables
S = ZZ/32003[a,b,c,d,f,g,s,t,w,x,y,z,MonomialOrder=>Lex]
phi = map(S,R,matrix{{a,b,c,d,f,g,random kk,random kk,random kk,s,t,random kk,random kk,w,x,y,z}})
see phi J
independentSet = support first independentSets(phi J, Limit=>1)
gbTrace = 3
time first gbRationalReconstruction(phi J, independentSet)
-- check
