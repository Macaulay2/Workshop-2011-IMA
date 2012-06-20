newPackage(
        "PrimDecomposition",
        Version => "0.1", 
        Date => "",
        Authors => {{Name => "", 
                  Email => "", 
                  HomePage => ""}},
        Headline => "",
        DebuggingMode => true
        )

export {primdec, minAssPrimes, "Indeps", "Intersect", "FacGB", "MinPrimes",
     getIndependentSets,
     makeFiberRings,
     decomp,
     factors,
     minSatSingular,
     "TestIdeal",
     "OriginalIdeal",
     "toAmbientField",
     "fromAmbientField"
     }




--------------------------------
-- Support routines ------------
--------------------------------

RingMap List := (F, L) -> L/(f -> F f)

quotMinSingular = (I, facs, F) -> (
    J := quotient(I,F); -- TODO: try to do this quotient iteratively, starting
                        -- with small factors
    if I == J then return (I, facs, F); -- is the 3rd argument really F?
    if #facs === 1 then return (J, facs, F);
    i := 0;
    while i < #facs and #facs > 1 do (
    	 fac1 := drop(facs,{i,i});
	 G := product fac1;
	 J1 := quotient(I,G);
	 if J == J1 -- if isSubset(J1, J) -- (since J \subset J1 always)
	 then (
	      facs = fac1;
	      F = G;
	      )
	 else i = i+1;
	 );
    {J,facs,F}
    )

minSatSingular = method()
minSatSingular(Ideal, List) := (I, L) -> (
     -- I is an ideal
     -- L is a list of irred polynomials (all different, all monic, all of positive degree)
     -- returns (Isat, F)
     --   where: Isat = saturate(I, product L)
     --   and       F = some product of the terms of L (with multiplicity)
     --                 s.t. Isat = I : F
     R := ring I;
     if #L === 0 then 
         (I, 1_(ring I))
     else (
	 L = sort L; -- TODO: fix this order
	 F := product L;
	 val := (I, L, F);  -- loop invariant: 
	 resultF := 1_R;
	 Iprevious := ideal(0_R);
	 firsttime := true;
	 while Iprevious != val#0 do (  -- isSubset(...)
	      if not firsttime then resultF = resultF * val#2;
	      Iprevious = val#0;
	      val = quotMinSingular val;
	      firsttime = false;
	      );
	 (val#0, val#2)
     )
)

factors = (F) -> (
     R := ring F;
     facs := if R.?toAmbientField then (
	  F = R.toAmbientField F;
     	  numerator factor F)
        else factor F;
     facs = apply(#facs, i -> (facs#i#1, (1/leadCoefficient facs#i#0) * facs#i#0 ));
     facs = select(facs, (n,f) -> # support f =!= 0);
     if R.?toAmbientField then apply(facs, (r,g) -> (r, R.fromAmbientField g)) else facs
     )

{*
factorize = method()
factorize RingElement := (F) -> (
     -- TODO: if over a fraction ring, need to lift, then factor, then put back
     -- this returns a list of {r, f}, where F is the product of all f^r, up to an 
     -- element of the base ring (i.e. all f returned will have degree at least one)
     --
     -- TODO: how should these be ordered?
     facs := factor F;
     facs = facs//toList/toList/reverse;
     select(facs, (r,f) -> first degree f > 0)
     )
*}

makeFiberRings = method()
makeFiberRings(List) := (baseVars) -> (
   -- This function takes an ideal I and a list of variables baseVars as input
   -- and returns a pair of matrices (mons, cs) where mons are the monomials in the ideal
   -- of lead terms of a gb of I, and cs are the coefficients, but with respect to
   -- a product order kk[fiberVars][baseVars].  See example below for behavior
   if #baseVars == 0 then error "expected at least one variable in the base";
   R := ring baseVars#0;
   if any(baseVars, x -> ring x =!= R) then error "expected all base variables to have the same ring";
   allVars := set gens R;
   fiberVars := rsort toList(allVars - set baseVars);
   baseVars = rsort baseVars;
   RU := (coefficientRing R) monoid([fiberVars,baseVars,MonomialOrder=>Lex]);
	     --MonomialOrder=>{#fiberVars,#baseVars}]);
   KK := frac((coefficientRing R)[baseVars]);
   KR := KK[fiberVars, MonomialOrder=>Lex];
   KR.toAmbientField = map(frac RU,KR);
   KR.fromAmbientField = (f) -> (if ring f === frac RU then f = numerator f; (map(KR,RU)) f);
   numerator KR := (f) -> numerator KR.toAmbientField f;
   denominator KR := (f) -> denominator KR.toAmbientField f;
   (RU, KR)
   )

minimalizeOverFrac = method()
minimalizeOverFrac(Ideal, Ring) := (I, S) -> (
     -- I is an ideal in a ring with an elimination order (maybe Lex)
     -- S is of the form k(basevars)[fibervars].
     -- If G is a GB of I, then G S is a GB if I S.
     -- this function returns a reduced minimal Groebner basis of I S, as a list
     -- of polynomials (defined over S).
     -- caveat: ring I must have either a Lex order or a product order, compatible with
     --  fibervars >> basevars.
     G := flatten entries gens gb I;
     sz := G/size; -- number of monomials per poly, used to choose which elem to take
     GS := flatten entries sub(gens gb I, S);
     minG := flatten entries mingens ideal(GS/leadMonomial);
     GF := for mon in minG list (
	  z := positions(GS, f -> leadMonomial f == mon);
	  i := minPosition (sz_z);
	  GS_(z#i));
     coeffs := GF/leadCoefficient;
     (flatten entries gens forceGB matrix{GF}, coeffs)
     )

zeroDimRadical = method()
zeroDimRadical Ideal := (I) -> (
     R := ring I;
     allvars := set gens R;
     for x in gens R list (
	  elimvars := toList(allvars - set {x});
	  fx := eliminate(I, elimvars);
	  facs := factors fx_0;
	  --if all(facs, f1 -> first f1 === 1) then continue;
	  if #facs === 1 and facs#0#0 === 1 then continue;
	  facs
	  )
     )

contractToPolynomialRing = method()
contractToPolynomialRing(Ideal) := (I) -> (
     -- assumes: I is in a ring k(basevars)[fibervars] created with makeFiberRings
     -- returns the intersection of I with k[fibervars,basevars] (also created with makeFiberRing).
     --   note: numerator (and denominator) of element in ring I gives an element in k[fibervars,basevars]
     newI := I_*/numerator//ideal//trim;
     denoms := I_*/denominator;
     denomList := unique flatten for d in denoms list (factors d)/last;
     << " denoms = " << denoms << " and denomList = " << denomList << endl;
     Isat := newI;
     for f in denomList do Isat = saturate(Isat, f);
     Isat
     )
///
  restart
  newPackage "PrimDecomposition"
  R = ZZ/32003[a..f, MonomialOrder=>Lex]
  
///

computeLexGB = method()
computeLexGB(Ring, Ideal, RingElement) := (Rlex, I, hilbfcn) -> (
     -- TODO: use the one in newGTZ
     J := sub(I, vars Rlex);
     gb J; -- TODO: use hilb fcn, and whatever else we can!
     J
     )

zeroDecompose = method()
zeroDecompose(Ideal, Ideal, Ideal) := (I,Isat,testIdeal) -> (
     -- Needs to be rewritten to not use the original primaryDecomposition...!
     Qs := primaryDecomposition Isat;
     Ps := associatedPrimes Isat;
     pos := positions(Qs, Q -> (gens testIdeal) % Q != 0);
     apply(Qs_pos, Ps_pos, (Q,P) -> (Q,P))
     )

minSat = method()

decomp = method(Options=>{Strategy=>null, TestIdeal => null, OriginalIdeal => null, Limit=>infinity})
decomp Ideal := opts -> (I) -> (
     -- rings in use here:
     --  R: original ring
     --  Rlex: same, lex order
     --  Rgrevlex: same, grevlex order
     --  S: lex order, in a different set of vars
     --  SF: lex order over a frac field, compatible with S
     R := ring I;
     if I == 0 then return {(I,I)};
     hilbfcn := if isHomogeneous I then poincare comodule I else null;
     if isHomogeneous I and dim I == 0 then return {(I, ideal gens R)};
     -- step 1: first compute a lex GB...
     Rlex := newRing(R, MonomialOrder=>Lex);  -- ring gnir in decomp.
     backToR := map(R,Rlex, vars R);
     Rgrevlex := newRing(R, MonomialOrder=>GRevLex); -- or use weight order??
     Jgrevlex := sub(I, Rgrevlex);  -- TODO: compute or grab gb of this
     -- compute gb of I in this order: ***
     J := computeLexGB(Rlex, I, hilbfcn); -- J is now in the ring Rlex
     -- some book-keeping:
     originalIdeal := if opts.OriginalIdeal then sub(opts.OriginalIdeal, Rlex) else ideal(1_Rlex);
     testIdeal := if opts.TestIdeal then sub(opts.TestIdeal, Rlex) else J;
     -- now for a few special cases
     if J == 1 then return {(ideal(1_R), ideal(1_R))};
     -- TODO: also bring testIdeal to Rlex (ser, peek)  ***
     -- step: clear out elements which have linear lead terms  ***
       -- this recursively calls decomp
       --   then put the result into the original ring, and return.
     -- special case: ring now has  1 variable
     if numgens R === 1 then (
     	  facs := factors(J_0);
     	  return for f in facs list (ideal (backToR f#1^f#0), ideal(backToR f#1));
	  );
     -- special case: dim J == 0.
     if dim J == 0 then (
     	  result := zeroDecompose(J, J, testIdeal); -- ***
     	  return backToR result;
	  );
     -- now comes the real algorithm
     result = {};
     -- step: now find maximal indep sets, and use that to split the ideal.
     indepSets := independentSets(J, Limit => opts.Limit);
     J1 := J; -- loop variable in the following:
     for basevars in indepSets do (
     	 (RFiberLex, RFiberFrac) := makeFiberRings basevars;
	 Jlex := sub(J1, RFiberLex); -- NOTE: it is possible that RFiberLex == Rlex, if so Jlex should be above J!
	    -- TODO: compute GB of Jlex (if not done.  Use hilb function, etc)
         (JFrac, coeffs, h) := minimalizeOverFrac(Jlex, RFiberFrac);
	 (Jsat, g) := minSat(J, coeffs); -- computed over a grevlex ring.  decomp does this step later, why??
	 PQs := zeroDecompose(JFrac, Jsat, TestIdeal => sub(testIdeal, RFiberFrac));
	 PQs = for PQ in PQs list (
	      -- substitute to Rlex
	      -- saturate wrt coefficients (computed over grevlex ring)
	      );
	 result = join(result, PQs);  -- what ring are these in?
	 J1 = J + ideal(g);
	   -- and compute a GB of this with as little work as possible
	   -- once the dim of J1 drops, don't bother continuing in this loop
	 -- the commputation of the new testIdeal should be done in Rgrevlex
	 testIdeal = intersect(testIdeal, Jsat); -- BUT: over Rgrevlex!  Why not do this earlier??
	 if #PQs > 0 then (
	      -- need to compute more about test ideal??
	      )
         );
     -- decomp: uses lower dimensional indep sets here
     -- after that: now decompose J1:
     backToR join(result, decomp(J1, TestIdeal=>testIdeal, OriginalIdeal=>I))
     );
    


getIndependentSets = method(Options => options independentSets)
getIndependentSets(Ideal) := opts -> (I) -> (
     indeps := independentSets(I, Limit=>opts.Limit);
     -- for each element, create two rings:
     --  product order ring
     --  frac field ring
     indeps
     )

vectorSpaceDimension = method()
vectorSpaceDimension Ideal := (I) -> (
     -- hopefully we are using this in a place where 'forceGB gens I' works.
     -- TODO: check that it is 0-dimensional too, give error if not.
     degree ideal leadTerm gens gb I
     )

end

-------------------------
simplifyIdeal = method()
simplifyIdeal Ideal := (I) -> (
     -- returns a pair (I', phi),
     -- where phi : R --> R, and
     -- phi(I') = I, and all variables which occured only linearly have been replaced with variables.
     )

isContainedInRadical = method()

primDecomp = method(Options => {Strategy=>null})
  -- return type: list of {primary,prime}

minAssPrimes = method(Options => {FacGB => false, Strategy=>null})
  -- return type: list of {prime}
  -- the list is the irredundant set of minimal primes.
minAssPrimes Ideal := opts -> (I) -> (
     -- step 1: handle special case: I == 0
     -- (also: check ring, and either put it into the correct form, or give error if cannot)
     minAssFcn := if opts.Strategy === GTZ then minAssGTZ else minAssSL;
     P0 := ring I;
     -- define a new ring P, in grevlex, same number of vars
     -- bring I into P.
     -- parse input options
     
     (I', map1) := simplifyIdeal I;
     gb I';  -- if map1 != identity, then we need to compute this here
     if I' == 1 then return {I'};
     if dim I' == 0 then (
	  -- use Moeller-H. algorithm
	  -- create a lex order ring
	  -- if vdim(I')  
	  return result;
	  );
     if not opts.FacGB then (
	  result = minAssFcn(I');
	  result = removeRedundants(result);
	  return (map1 result);
     	  );
     comps := facGB I';
     result = comp/minAssFcn//removeRedundants;
     map1 result);

minAssSL = (I) -> (
     local pd;
     result := {};
     P := ideal(1_(ring I));
     while (
	  pd = minAssSLIteration(I,P);
	  pd =!= null
     ) do (
	  P = intersect(P, pd#1);
	  result = join(result, pd#0);
	  );
     result
     )

minAssGTZ = (I) -> ()

minAssSLIteration = method()
minAssSLIteration(Ideal, Ideal) := (I,P) -> (
     -- input: ideal I
     --        ideal P, which is the intersection of some components of I
     -- output: (components, P')
     --   where components is a list of different minimal components of I (from those in P)
     --   and P' is the intersection of these components
     k := position(P_*, f -> not isContainedInRadical(f, I));
     if k =!= null then return null;
     J := saturate(I, P_k);
     -- now compute some of the components of J
     newDecompStep(J, Indeps=>1, Intersect=>true, Strategy=>2)
     )


-- questions:
--  1. what are seri, peek?
--  2. 
newDecompStep = method(Options=>{Indeps=>1, Intersect=>true, Strategy=>2})
newDecompStep Ideal := opts -> (I) -> (
{*     
     R := ring I;
     if isHomogeneous I then (
	  if dim I === 0 then return ({ideal vars ring I}, ideal vars ring I);
	  hf := poincare I;
	  );
     if I == 0 then return ({I}, I);
     -- 
     R1 := newRing(ring I, MonomialOrder=>Lex);
     J := sub(I, R1);
     -- also compute the reduced GB of J:
     --   if R1 === R, then already done
     --   if not, but J is homog, then use the hilbert function to compute GB
     --     else, just compute GB
     gbJ := computeLexGB J;
     -- step: gbJ --> (fried, gbJ), where 
     --   fried consists of the elements with linear lead term
     --   and gbJ consists of all the rest
     fried := for f in gbJ list if deg(leadMonomial f) == 1 then ...
     if #fried == numgens ring I then return ({I}, I);
     if #fried > 0 then (
	  -- create a lex polynomial ring with just the variables not
	  -- occuring as lead terms of 'fried'
	  -- then map gbJ to this ring, and recurse
	  -- then map these back, and return this result
	  return ...
	  );
     if I == 1 then return (....);
     -- handle the case when R1 has 1 variable:
     if numgens R1 then (
	  -- factor the generator of gbJ
	  -- create the PD from this factorization, and return
	  );
     -- the zero-dimensional case
     if dim J == 0 then (
	  result := newZeroDecomp(J, ser, Strategy=>opts.Strategy);
	  return (cleanPrimary result, J);
	  );
     -- now find a maximal indep set
     --
     -- in @Phelp (same ring as R, except with grevlex, if R was not weighted, grevlex)
     -- compute a GB of I, call it jwork
     --
     -- 
*}
     )

newReduction = method()
newReduction(Ideal, Ideal, List) := (J, currentIntersection, baseVars) -> (
     -- return a list of what??
     -- what are we assuming here??
     result := {}; -- list of either {ideal, null}, or {Q:ideal, P:ideal},
                   -- where P is a prime, and Q is primary
     -- if indepSet consists of >0 variables, create a new ring, in product order
     (FiberRing, GenericFiberRing) := makeFiberRings baseVars; -- need ring maps too?
     -- step: bring J, currentIntersection into FiberRing
     -- step: compute gb of J in FiberRing, using (if homogeneous) hilb fcn
     -- step:
     currentIntersection = sub(currentIntersection, FiberRing);
     Jnew := sub(J, FiberRing);
     if isHomogeneous J then 
         Jnew.poincare = poincare J;
     gbJ := gens gb Jnew; -- computes using Hilbert function if possible
     sizes := gbJ/size; -- list of number of monomials, for use in choosing 
                       -- which elements of gb of H
     vv := findMinimalGB(sub(leadTerm(1,gbJ), GenericFiberRing), sizes);
     -- now prune out gbJ, or return it in the first place??
     leadGbJ := gbJ/leadCoeff;
     -- now call zero dimensional code (over the fraction field)
     primaryList := newZeroDecomposition(leadGbJ,currentIntersection, Compute=>MinPrimes);
     -- now we need to bring these back into the poly ring
     -- for each elem in primaryList (note: each is a GB over the fraction field)
     --  first get the lead terms
     -- now we work in FiberRing:
     --  grab the coeffs from the primaryList.
     --  
     )
testPrimary = method()

zeroDecomposition = method(Options=>{Return=>MinPrimes})
zeroDecomposition(Ideal, Ideal) := opts -> (I, answerSoFar) -> (
     -- input: I:  an ideal, 0-dimensional, likely over a fraction ring.  I should be a minimal GB, not nec reduced though.
     -- output: a list of:
     --  (Q, P),  P is prime, and Q is P-primary,
     --     if P is instead null, then Q is possibly not primary.
     --  If opts.Return is MinPrimes, then the result is a list of:
     --  (P, P), or (P, null), meaning P is not proved to be a prime ideal
     if dim I > 0 then error "zeroDecomposition expected a 0-dimensional ideal";
     I = interReduce I; -- CHECK exactly what this does over frac fields, but I should now be a reduced GB over frac field,
                        -- in a poly ring in Lex order
     vecDim := vectorSpaceDimension I;
     -- case 0: I = (1).  Return {}.
     -- case 1: the GB has a polynomial f(x_n) of degree vecDim.  This is a good caase!
     --  in this case, the GB looks like (f(xn), x_(n-1) - ..., ..., x_1 - ...), so replacing f with an irred  factor 
     --   (or prime power factor of an irredu) retains that this is a GB (but usually needs to be reduced).
     --  in this case we have the complete answer with no further (hard) work.  BUT: for each component, only place it on,
     --  if it does not contain answerSoFar.
     -- case 2: I is homogeneous (w.r.t. fiber vars, of course)
     --  then I is primary to the homog max ideal, so return with that.
     --  BUT: first make sure that I is not larger than answerSoFar
     -- 
     facs := factors I_0; -- this takes care of moving back to a poly ring to do the factorization.
     -- now we attempt to split I as much as possible, without doing random change of coordinates
     
     -- now we need to change coordinates, too bad.
     )

splitComponent = method()
splitComponent(Sequence, Ideal) := (PQ, answerSoFar) -> (
     (Q,P,vecdim,isprimary) := PQ;
     if isprimary then return {PQ};
     if isSubset(answerSoFar, Q) then return {};
     if isHomogeneous Q then return {(Q, ideal gens ring Q, vecdim, true)};
     result := {};
     -- loop through each element of Q_*
     for f in Q_* do (
       facs := factors f; -- this only keeps factors of degree > 0.
       -- if there is one factor of degree = vecdim, we are done:
       if #facs === 1 and vecdim == first degree facs#0#0 then (
	    -- there is only one component, and it is prime
	    result = append(result, (P,P,vecdim,true));
	    return result;
	    );
       );
       if #facs === 1 and facs#0#1 > 1 then (
	    P = interReduce(P + ideal facs#0#0);
	    if isHomogeneous P then (
		 P = ideal gens vars ring Q;
		 result = append(result, (Q,P,vecdim,true));
		 return result;
		 );
	    );
       -- now we check: if all of the factors g_i satisfy for i != j, g_i + g_j == (1),
       -- then Q = (Q + g_1^a_1) + ... + (Q + g_r^a_r).
       -- we don't yet know if these are primary, but we'll recurse and find out.
       if pairWiseDisjoint(facs/first) then (
	    -- TODO: split using the factorization
	    result;
	    )
       else
            split(PQ, facs#0)
     )

splitZeroDimensional = method() -- splitPrimary in primdec.lib
splitZeroDimensional(List, Ideal) := (PQs, answerSoFar) -> (
     -- 2 cases: computing PD, or minprimes.
     -- PQs is a list of Q=(I+ (g_i^a_i), P=(I + g_i), totaldim, isPrimary:Boolean)
     --  where each Q is zero-dimensional (and Q \cap k[last var] = g_i^a_i).
     -- 
     -- Here, we have a TODO list of such components.  And we collect answers: these are components
     --   that are either primary, or that we choose not to handle.
     -- Perhaps instead, we should hav a routine that takes one such component, and returns a list.
     --  then this routine processes that list over and over until it gets tired
     --
     -- Note that everything is equidimensional, same 0-dimension.  If N is the degree (vector space dim of quotient)
     -- then the sum of all vector space quotients returned must add up to N.
     TODO := PQs;
     result := {};
     while #TODO > 0 do (
	  PQ := TODO#0;
	  TODO = drop(TODO,1);
	  (result1, todo1) := splitComponent(PQ, answerSoFar);
	  result = join(result, result1);
	  TODO = append(TODO, todo1);
	  );
     result
     )

beginDocumentation()

doc ///
Key
  PrimDecomposition
Headline
  looking at singular algorithms
Description
  Text
  Example
Caveat
SeeAlso
///

end

doc ///
Key
Headline
Usage
Inputs
Outputs
Consequences
Description
  Text
  Example
  Code
  Pre
Caveat
SeeAlso
///

TEST ///
-- test code and assertions here
-- may have as many TEST sections as needed
///

restart
loadPackage "PrimDecomposition"

R1 = QQ[a..M, MonomialSize => 8]
I1 = ideal(K,J,I,E,D,A,v,s,r-G,q-t,o,m-w,l-y,k-z,j-t,i-L,g,f,d,c-n,b-H,a,G*M-t,z*M-w,y*M-p, H*L-C,B*L-H,z*L-G,w*L-t,t*L-x,n*L-h,e*L-y,B*G-z*H,y*F-G,p*F-t,e*F-z,B*C-H^2,z*C-G*H,w* C-t*H,t*C-x*H,n*C-h*H,e*C-y*H,y*B-e*H,x*B-t*H,t*B-w*H,h*B-n*H,y*z-e*G,x*z-t*G,t*z-w*G, h*z-n*G,w*y-p*z,t*y-p*G,e*x-p*G,t^2-w*x,n*t-h*w,h*t-n*x,e*t-p*z,e*h-n*y,e*H*M-p*B,p*G* L-x*y,p*C*G-x*y*H,p*z*B-e*w*H,p*z^2-e*w*G,n*x*y-h*p*G,h^2*w-n^2*x)
indeps = getIndependentSets I1
#indeps
makeFiberRings(support indeps#0)
indeps / (makeFiberRings @@ support)

---------- example ------------------
R1 = ZZ/32003[a,b,c,d,e,f,g,h]
I1 = ideal(a+c+d-e-h,
   2*d*f+2*c*g+2*e*h-2*h^2-h-1,
   3*d*f^2+3*c*g^2-3*e*h^2+3*h^3+3*h^2-e+4*h,
   6*b*d*g-6*e*h^2+6*h^3-3*e*h+6*h^2-e+4*h,
   4*d*f^3+4*c*g^3+4*e*h^3-4*h^4-6*h^3+4*e*h-10*h^2-h-1,
   8*b*d*f*g+8*e*h^3-8*h^4+4*e*h^2-12*h^3+4*e*h-14*h^2-3*h-1,
   12*b*d*g^2+12*e*h^3-12*h^4+12*e*h^2-18*h^3+8*e*h-14*h^2-h-1,
   -24*e*h^3+24*h^4-24*e*h^2+36*h^3-8*e*h+26*h^2+7*h+1)
loadPackage "PrimDecomposition"
debug PrimDecomposition
decomp I1
independentSets ideal oo8
independentSets I1

-- Testing minSat stuff
  R = ZZ/32003[a,b,c,d,e,h]
  I = ideal(
         a+b+c+d+e,
	 d*e+c*d+b*c+a*e+a*b,
	 c*d*e+b*c*d+a*d*e+a*b*e+a*b*c,
	 b*c*d*e+a*c*d*e+a*b*d*e+a*b*c*e+a*b*c*d,
	 a*b*c*d*e-h^5)
  basevars = support first independentSets I
  (S,SF) = makeFiberRings basevars
  describe S
  describe SF
  IS = sub(I,S)
  gens gb IS;
  minimalizeOverFrac(IS, SF)
