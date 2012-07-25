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
     minimalizeOverFrac,
     decomp,
     factors,
     minSatSingular,
     simplifyIdeal,
     "TestIdeal",
     "OriginalIdeal",
     "toAmbientField",
     "fromAmbientField"
     }


-- Functions we should have:
--  isPrime
--  isPrimary
--  isRadical
--  isEquidimensional
--  
--  minimalPrimes
--  radical
--  unmixedRadical
--  associatedPrimes
--    associatedPrimeWitness(PD, P)
--  primaryDecomposition

--  multiplicity(Ideal, Ideal)
--
-- Helper routines:
--  splitting functions: via indeps (and using quotients only, or using splitting polys), use all indeps/one indep?
--                       "easy" factorization (gens or gb)
--                       factorization (gens or gb)
--  extendIdeal
--  contractToPolynomialRing
--  splitZeroDimensional: first make sure each g_i is k-irreducible.
--    can we make sure GB is just g1, ..., gn too?
--  randomLastCoordinate
--    change coordinates (with ring map to/from), on only a smaller number of variables.
--  getNonLinearPart -- given a 0-dim GB {g1,...,gn}
--     return the elements gi, g_(i+1), ..., gn, where in(gi) != xi.
--  minimalizeOverFrac
--  makeFiberRings

--------------------------------
-- Zero-dimensional ideals -----
--------------------------------

-- Routines needed:
--    isZeroDimensionalPrimeGeneralPosition
--    testZeroDimensionalPrimaryGeneralPosition (returns null, or a lex GB of a prime in general position)
--    randomLast (returns ring map, and its inverse, randomizing the last variable)
--    splitZeroDimensional (splits the ideal into as many parts as possible)


------------------------------
-- Radical containment -------
------------------------------

-- helper function for 'radicalContainment'
radFcn = (I) -> (
     if not I.cache#?"RadicalContainmentFunction" then (
     	  R := ring I;
     	  n := numgens R;
     	  S := (coefficientRing R) (monoid[Variables=>n+1,MonomialSize=>16]);
     	  mapto := map(S,R,submatrix(vars S,{0..n-1}));
     	  I = mapto I;
     	  A := S/I;
	  rad := (g) -> (g1 := promote(mapto g, A); g1 == 0 or ideal(g1 * A_n - 1) == 1);
	  I.cache#"RadicalContainmentFunction" = rad;
	  );
     I.cache#"RadicalContainmentFunction"
     )

radicalContainment = method()

-- Returns true if g is in the radical of I.
-- Assumption: I is in a monomial order for which you are happy to compute GB's.x
radicalContainment(RingElement, Ideal) := (g,I) -> (radFcn I) g

-- Returns the first index i such that I_i is not in the radical of J,
--  and null, if none
-- another way to do something almost identical: select(1, I_*, radFcn J)
radicalContainment(Ideal, Ideal) := (I,J) -> (
     rad := radFcn J;
     G := I_*;
     for i from 0 to #G-1 do if not rad G#i then return i;
     null)

TEST ///
  restart
  debug loadPackage "PrimDecomposition"
  R = ZZ/32003[a..f]
  F = map(R,R,symmetricPower(2,matrix{{a,b,c}}))
  I = ker F
  J = I^2
  G = I_0
  assert radicalContainment(G,J)
  assert not radicalContainment(G-a^2,J)
  assert (radicalContainment(I, I^2) === null)
///

--------------------------------   



--------------------------------
-- Support routines ------------
--------------------------------

cleanFactorList = method(Options => {Strategy=>0})
cleanFactorList List := opts -> (L) -> (
     -- input: list of polynomials
     -- output: a list of distinct monic squarefree polynomials
     -- Strategy=>0: sort in size, then asc degree
     -- Strategy=>1: sort in desc degree, then monorder of lead term
     -- Strategy=>2: sort in asc degree, then monorder of lead term
     facs := select(L, f -> # support f > 0);
     facs = facs/factors//flatten/last//unique;
     if opts.Strategy === 0 then 
          facs/(f -> (- first degree f, size f, f))//sort/last
     else if opts.Strategy === 1 then (
       	  matrixL := matrix{facs};
       	  -- Curiously, it seems that in the Huneke example below, Ascending is faster.  How can one decide which order to choose?
       	  flatten entries matrixL_(sortColumns(matrixL, DegreeOrder=>Descending))
       	  )
     else if opts.Strategy === 2 then (
       	  matrixL = matrix{facs};
       	  -- Curiously, it seems that in the Huneke example below, Ascending is faster.  How can one decide which order to choose?
       	  flatten entries matrixL_(sortColumns(matrixL, DegreeOrder=>Ascending))
	  )
     else error "unknown Strategy in cleanFactorList"
     )

RingMap List := (F, L) -> L/(f -> F f)

smartQuotient = (I,L) -> (
   -- Input: An ideal I and a list of RingElements L
   -- Output: I:(product L) but iteravely instead by computing quotients with small factors first
   matrixL := matrix {select(L, f -> not isConstant f)};
   -- Curiously, it seems that in the Huneke example below, Ascending is faster.  How can one decide which order to choose?
   --sortedL := flatten entries matrixL_(sortColumns(matrixL, DegreeOrder=>Ascending));
   sortedL := flatten entries matrixL_(sortColumns(matrixL, DegreeOrder=>Descending));
   result := I;
   -- this is the command that is slowing things down.  It seems a single call to quotient is better in some cases, but order certainly matters.
   scan(L, f -> result = quotient(result,f));
   result
)

quotMinSingular = (I, facs, F) -> (
    -- Input: An ideal I, a list of RingElements facs, and a RingElement F, which is the
    --        product of facs
    -- Output: A triple (J, facs, F)  J = (I:F) (where F is the input F), facs is a subset of the input facs, and F = product of the new facs.
    --         Some work is done to find the smallest subset of facs for which this is true, so that F is of (relatively) small degree.  
    --         This code does not match SINGULAR *exactly* since they start the computation of quotients over again any time an element is dropped from the list.
    --time J := smartQuotient(I,facs);   -- smartQuotient attempts to compute the quotient iteravely since we have a factorization of F already.   
    time J := quotient(I,F);
    if I == J then return (I, facs, F); -- is the 3rd argument really F?
    if #facs === 1 then return (J, facs, F);
    i := 0;
    while i < #facs and #facs > 1 do (
    	 fac1 := drop(facs,{i,i});
	 G := product fac1;
	 --time J1 := smartQuotient(I,fac1);
	 time J1 := quotient(I,G);
	 if J == J1 -- if isSubset(J1, J) -- (since J \subset J1 always)
	 then (
	      facs = fac1;
	      F = G;
	      )
	 else i = i+1;
	 );
    (J,facs,F)
    )

minSatSingular = method()
minSatSingular(Ideal, List) := (I, L) -> (
     -- I is an ideal
     -- L is a list of irred polynomials (all different, all monic, all of positive degree)
     -- L typically is the list of positive degree denominators that arise from a call to minimalizeOverFrac (Is this right?)
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

doesFactor = (F) -> (
     facs := factors F;
     #facs > 1 or facs#0#0 > 1
     )

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
     phi := map(ring I, S);
     sz := G/size; -- number of monomials per poly, used to choose which elem to take
     GS := flatten entries sub(gens gb I, S);
     minG := flatten entries mingens ideal(GS/leadMonomial);
     GF := for mon in minG list (
	  z := positions(GS, f -> leadMonomial f == mon);
	  i := minPosition (sz_z);
	  GS_(z#i));
     coeffs := GF/leadCoefficient/phi;
     (flatten entries gens forceGB matrix{GF}, coeffs)
     )

-- Poorly named:
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

extendIdeal = method()
extendIdeal Ideal := (I) -> (
     -- I is an ideal
     -- returns an ideal whose elements are a reduced GB of I k(indepset)[fibervars]
     indep := support first independentSets I;
     (S,SF) := makeFiberRings indep;
     IS := sub(I, S);
     time gens gb IS;
     (JSF, coeffs) := minimalizeOverFrac(IS, SF);
     ideal JSF
     )

computeLexGB = method()
computeLexGB(Ring, Ideal, RingElement) := (Rlex, I, hilbfcn) -> (
     -- TODO: use the one in newGTZ
     J := sub(I, vars Rlex);
     gb J; -- TODO: use hilb fcn, and whatever else we can!
     J
     )

----------------------------------------------------
-- "Remove" polynomials which occur as variables ---
----------------------------------------------------
-- Input: ideal I in a polynomial ring
-- Output: (J:Ideal, F:RingMap)
--   where F:R-->R is a ring map s.t. F J == I
--   and J has the polynomials defining a variable x as linear, has  the corresp poly = x.
simplifyIdeal = method()
simplifyIdeal Ideal := (originalI) -> (
     -- input: ideal I in a polynomial ring R
     -- output: (J, phi), J is an ideal in the same ring
     --                   phi : R --> R
     -- such that the only generators of J which are linear in a variable are themselves 
     -- variables, and phi J == I
     I := originalI;
     R := ring I;
     H := new MutableList from gens R;
     for x in gens R do (
	  k := position(I_*, f -> first degree diff(x,f) == 0);
	  if k === null then continue;
	  c := leadCoefficient diff(x,I_k);
	  g := I_k - c*x;  
	  -- at this point f = I_k = c*x + g, and g does not involve x.
	  --  (and c is a constant)
	  p := - 1/c * g;
	  I = ideal(x) + ideal compress sub(gens I, x=>p);
	  H#(index x) = x - p;
	  );
     (ideal compress gens I, map(R,R,toList H))
     )

TEST ///
  restart
  debug loadPackage "PrimDecomposition"
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
  (J,phi) = simplifyIdeal I
  J1 = ideal gens phi J
  assert(I == J1)
  codim I
  time CJ = splitEquidimFactors J;
  time CI = splitEquidimFactors I;
  assert(intersect CJ == J)
  assert(intersect CI == I)
  ans1 = CJ/(i -> flatten entries gens gb  phi i)
  ans2 = CI/(i -> flatten entries gens gb i)
  assert(ans1 === ans2)
///

-----------------------
-- Splitting methods --
-----------------------
splitBy = (I, h) -> (
     Isat := saturate(I, h);
     f := 1_(ring I);
     while not isSubset(f*Isat, I) do f = f*h;
     if Isat == I or Isat == 1 then error ("alas, your element "|toString h|" is not a splitting element");
     if f == 1 then null else (Isat, trim(I + ideal f))
     )

splitUsingQuotientsBy = (I, h) -> (
     Isat := saturate(I, h);
     I2 := I : Isat;
     if Isat == I or Isat == 1 then (
	  return null
	  );
     if intersect(Isat, I2) == I then (
	  return (Isat, I2);
	  );
     << "second ideal might introduce non-redundancy" << endl;
     f := 1_(ring I);
     while not isSubset(f*Isat, I) do f = f*h;
     if Isat == I or Isat == 1 then error ("alas, your element "|toString h|" is not a splitting element");
     if f == 1 then null else (Isat, trim(I + ideal f))
     )

splitViaIndep = method()
splitViaIndep Ideal := (I) -> (
     indeps := independentSets I;
     indep := support first indeps;
     << "Number of independent sets: " << #indeps << endl;
     << "  Choosing: " << indep << endl;
     (S, SF) := makeFiberRings indep;
     IS := sub(I, S);
     gens gb IS;
     (ISF, coeffs) := minimalizeOverFrac(IS, SF);
     G := (factors product coeffs)/last//product;
     << "  the factors of the flattener: " << netList((factors G)/last) << endl;
     G = sub(G,ring I);
     J1 := saturate(I, G);
     J2 := I: J1;
     if intersect(J2,J1) == I then (
	  << "  Yes! Quotient method split the ideal" << endl;
	  return (J1,J2);
	  );
     << "  No! Need to manually determine the f^ell from lecture" << endl;
     (J1, G)
     )

splitViaIndeps = (I) -> (
     (J1, J2) := splitViaIndep I;
     if class J2 === Ideal and J2 != 1 then (
	      (equidims2, J) := splitViaIndeps J2;
	      return ({J1} | equidims2, J);
	      );
     ({J1}, J2)
     )


-- NOT YET FUNCTIONAL:
splitViaIndepNEWER = method()
splitViaIndepNEWER Ideal := (I) -> (
     indeps := independentSets I;
     indep := support first indeps;
     << "Number of independent sets: " << #indeps << endl;
     << "  Choosing: " << indep << endl;
     (S, SF) := makeFiberRings indep;
     IS := sub(I, S);
     gens gb IS;
     (ISF, coeffs) := minimalizeOverFrac(IS, SF);
     G := (factors product coeffs)/last//product;
     << "  the factors of the flattener: " << netList((factors G)/last) << endl;
     G = sub(G,ring I);
     J1 := saturate(I, G);
     J2 := I: J1;
     if intersect(J2,J1) == I then (
	  << "  Yes! Quotient method split the ideal" << endl;
	  return ((J1, indep, ISF),J2);
	  );
     << "  No! Need to manually determine the f^ell from lecture" << endl;
     ((J1, indep, ISF), G)
     )

-- NOT YET FUNCTIONAL:
splitViaIndepsNEWER = (I) -> (
     (J1, J2) := splitViaIndepNEWER I;
     if class J2 === Ideal and J2 != 1 then (
	      (equidims2, J) := splitViaIndepsNEWER J2;
	      return ({J1} | equidims2, J);
	      );
     ({J1}, J2)
     )

splitEquidimFactors = (I) -> (
     -- idea: loop through the gens of I.
     --   if any factors, then try to split the ideal.
     --     if it splits, call recursively on each elem of split, and return joined list.
     --     if not, continue to the next generator
     -- at the end, if it doesn't split, return {I}
     I1 := ideal gens gb I;
     for i from 0 to numgens I1 - 1 do (
	  facs := factors I1_i;
	  if #facs > 1 then (
	       split := splitUsingQuotientsBy(I, facs#0#1);
	       if split =!= null then return(split//toList/splitEquidimFactors//flatten);
	       )
	  );
     {I}
     )

-------------------------------------
-- Factorization over a tower -------
-------------------------------------
factorize = method()
factorize(RingElement, Ideal) := (F, I) -> (
     -- factor F mod I
     -- I = (g_(n-1), g_(n-2), ..., g_0) zero dimensional prime over a fraction field, in lex order
     -- F should be a polynomial in a ring R/I, univariate or multivariate?, monic?
     --
     -- steps:
     --  make change of basis xn = xn + c * x(n-1) + ... c' * x(0)
     --  find gb of (phi I, phi F)
     --    this shoud be of the form: xn^r + ..., rest of variables occur linearly
     --  factor this new poly (in one variable).
     --  if it doesn't factor over kk, then F is likely irreducible
     --  if it does, then F is NOT irreducible:
     --    in this case, for each factor, map back, and get gens gb(I + (factor))
     --    get a gb of form: original I, and one new element, the desired factor.
     
     --
     -- ASSUMPTIONS:
     --  1. SF = ring I was made with makeFiberRing
     --  2. F is a univariate polynomial in x over subring generated by variables appearing in I, where
     --     x is a variable occuring in SF
     --  3. F is monic in this variable (we will try to remove this requirement)
     --
     R := ring I;
     xset := toList(set gens ring F - set support I);
     if #xset > 1 then error "expected a univariate polynomial";
     r := last gens R;
     i := index first xset;
     J := I + ideal F;
     randomElem := sum for j from index first xset to numgens R - 2 list (random 10 * R_j);
     phi := map(R,R, {r => r + randomElem});
     phiInverse := map(R,R, {r => r - randomElem});
     J1 := phi J;
     G := first flatten entries gens gb J1;
     facs := factors G;
     --error "debug me";
     if #facs == 1 and facs#0#0 == 1 then return {(1, F)};
     -- otherwise there is a factorization!
     apply(facs, (n,f) -> (
	       f1 := last flatten entries gens gb (J + ideal phiInverse f);
	       (n,f1)
	       ))
     )

-------------------------------------
-- Zero dimensional minimal primes --
-- Experimentation code -------------
-------------------------------------
-- Given: equidimensional ideal, indep set, and the GB over lex over the frac field
--   Want: (a) find minimal primes
--         (b) determine if prime
--         (c) determine if primary, and if do, find the prime

decomposeZeroDimensional = method()
decomposeZeroDimensional(Ideal, List, Ideal) := (I, indep, IF) -> (
     -- I is an ideal wrt block order lex >> grevlex(indep)
     -- indep is a max indep set, s.t. I \cap k[indep] = (0).
     -- IF is a reduced GB for I k(indep)[fibervars].
     )

findPurePowers = method()
findPurePowers Ideal := (IF) -> (
     -- IF is a reduced lex GB for I k(indep)[fiber]
     -- returns the list of n (= #fiber) polynomials, s.t. i-th one has lead term x_i^(a_i),
     --   where x_i are the fiber variables
     select(IF_*, f -> # support leadTerm f == 1)
     )

splitPurePowers = method()
splitPurePowers Ideal := (IF) -> (
     L := findPurePowers IF;
     for f in L do (
	  facs := factors f;
	  if #facs == 1 and facs#0#0 == 1 then continue;
	  return flatten for fac in facs list splitPurePowers (ideal gens gb ((ideal fac#1) + IF));
	  );
     {IF}
     )

isZeroDimensionalPrime = method()
isZeroDimensionalPrime Ideal := (G) -> (
     -- Input: G is a reduced lex GB, zero-dimensional
     -- Output: true, if G can easily be determined to be prime
     --         false: not sure, or definitely not prime
     -- ASSUMPTION: if the ring of G is over a fraction field, the ring
     --  MUST have been constructed using 'makeFiberRings'
     --  otherwise, the call to 'factors' fails.
     -- WARNING: true means it IS prime.  false means it might be prime, it might be not prime.
     R := ring G;
     n := numgens R;
     if numgens G =!= n then return false;
     for i from 1 to n-1 do (
	  s := support leadTerm G_i;
	  if # support leadTerm G_i > 1 then return false;
	  if leadTerm G_i == R_(n-1-i) then continue;
	  if s =!= support G_i or doesFactor G_i then return false;
	  );
     not doesFactor G_0
     )

isZeroDimensionalPrime Ideal := (G) -> (
     -- Input: G is a reduced lex GB, zero-dimensional
     -- Output: true, if G can easily be determined to be prime
     --         false: not sure, or definitely not prime
     -- ASSUMPTION: if the ring of G is over a fraction field, the ring
     --  MUST have been constructed using 'makeFiberRings'
     --  otherwise, the call to 'factors' fails.
     -- WARNING: true means it IS prime.  false means it might be prime, it might be not prime.
     R := ring G;
     n := numgens R;
     if numgens G =!= n then return false;
     (vars, H) := prepareForPrimeSplit G;
     if numgens H > 1 
     then false
     else if numgens H === 0 then true
     else not doesFactor H_0
     )

TEST ///
  restart
  debug loadPackage "PrimDecomposition"
  R = ZZ/32003[a,b,c,d,e,h]
  (S,SF) = makeFiberRings {c} -- this is necessary currently so that 'factors' will work over the fraction field
  use coefficientRing SF
  use SF
  I1 = ideal(h^4-4*c*h^3+6*c^2*h^2+c^3*h+c^4,
       e+((-14547)/(c^2))*h^3+((-11637)/(c))*h^2-8728*h-11637*c,
       d^2+((-2909)/(c^2))*d*h^3+((-8729)/(c))*d*h^2-14547*d*h-8728*c*d+((-11636)/(c))*h^3-2913*h^2+5818*c*h-2910*c^2,
       b+d+((-2909)/(c^2))*h^3+((-8729)/(c))*h^2-14547*h-8728*c,
       a+((-14547)/(c^2))*h^3+((-11637)/(c))*h^2-8728*h-11637*c)
  assert not isZeroDimensionalPrime I1

  I2 = ideal(h^4+c*h^3+c^2*h^2+c^3*h+c^4,e^2+3*c*e+c^2,d+e+3*c,b-c,a-c)
  assert isZeroDimensionalPrime I2
///

prepareForPrimeSplit = (G) -> (
     -- input: Ideal, reduced lex GB
     -- output: (vars:List, J:Ideal)
     --   vars is a list of the variables x_i whose in(g_i) != xi
     --   J is a subset of the GB of G, consisting of polys in G which only involve 'vars'.
     --   vars: support of J, except the last variable
     R := ring G;
     linears := set for g in G_* list (
	  ing := leadTerm g;
	  s := support ing;
	  if #s > 1 then continue; -- not a variable
	  if ing != s_0 then continue;  -- not a variable
     	  s#0
	  );
     keep := set gens R - linears;
     H := select(G_*, g -> isSubset(set support g, keep));
     (keep, ideal H)  -- note: if G is a GB, so is H
     )

primeSplit = (I) -> (
     -- input: I is a reduced lex GB of a 0-dimensional ideal
     -- output: null, means that I is prime
     --         List: of factors f1, ..., s.t. I + (fi) is prime (or closer to prime??)
     --
     -- suppose that each g_i is irreducible over k
     -- this routine performs a random change of coordinates, to obtain a polynomial of
     --  which will hopefully split the ideal I (or prove that I is prime).
     (varlist, H) := prepareForPrimeSplit I;
     N := degree ideal leadTerm gens I; -- this is the vector space dim
     varlist = sort toList varlist;
     if # varlist <= 1 then return (true, null);
     x := varlist_0;
     varlist = drop(varlist, 1);
     randomElement := sum (varlist/(y -> (1 + random 10) * y));
     R := ring I;
     phi := map(R,R,{x => x + randomElement});
     phiInverse := map(R,R,{x => x - randomElement});
     H = phi H;
     h := (gens gb H)_(0,0);
     completelysplit := (leadTerm h == x^N);
     facs := factors h;
     if #facs == 1  and facs#0#0 == 1 
     then (true, null)
     else (completelysplit, apply(facs, (n,f) -> (n,(phiInverse f) % I)))
     )

minPrimesZeroDimensional = method()
minPrimesZeroDimensional Ideal := (I) -> (
     -- Input: reduced lex GB I, 0-dimensional
     -- Output: List of ideals, each is prime, and radical(I) == intersection of these ideals
     -- 
     L := splitPurePowers I;
     result := {};
     while #L > 0 do (
	  J := first L;
	  L = drop(L,1);
	  if isZeroDimensionalPrime J
	  then result = result | {J}
	  else (
	       << "calling primeSplit" << endl;
	       (completelysplit, fs) := primeSplit J;
	       if fs === null 
	       then result = result | {J}
	       else (
	       	    Js := apply(fs, (n,f) -> ideal gens gb (ideal f + J));
	       	    if completelysplit 
	       	    then result = result | Js
	       	    else L = L | Js;
		    );
	       )
	  );
     result
     )
---------------------------------
-- 0-dimensional PD routines ----
---------------------------------
-- For zero decomposition:
--  Keep this in mind:
--    1. split using factoring as much as possible
--    2. if the GB is larger than the g1, ..., gn, how can we use that to simplify/split ideal?
--    3. If we change variables, ignore the variables which occur linearly, both in the change of vars, and
--       in the new GB computation.  Should we do the new computation in S or SF?
--    4. How do we do the actual splitting?  Do we first change variables back to orig coordinates?
--    5. Should we use Seidenberg radical formula?
--    6. use testIdeal, originalIdeal ?
--    7. 
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
restart
loadPackage "PrimDecomposition"
debug PrimDecomposition

-- this example is not terribly interesting since only a single variable in basevars
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

-- Huneke example, certainly complicated enough to look at.
restart
debug loadPackage "PrimDecomposition"
R = QQ[s,t,u,x,y]
I = ideal"s15,t15,u15,u5 - s3tx + s2t2x + s2t2y - st3y"
basevars = support first independentSets I
(S,SF) = makeFiberRings basevars
describe S
describe SF
IS = sub(I,S)
gens gb IS;
minInfo = minimalizeOverFrac(IS, SF)
facs = cleanFactorList minInfo#1
time minSatSingular(IS,facs)
facs = minInfo#1
-- computing the quotient iteravely seems to slow down the computation in this example.  Am I doing something wrong?
time quotient(IS,product minInfo#1)
time smartQuotient(IS,minInfo#1)
minInfo#1 / factors
