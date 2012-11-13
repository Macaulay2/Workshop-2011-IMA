newPackage(
        "PD",
        Version => "0.1", 
        Date => "",
        Authors => {{Name => "", 
                  Email => "", 
                  HomePage => ""}},
        Headline => "New Primary Decomposition Implementation",
        DebuggingMode => true,
        AuxiliaryFiles=>true
        )

needs "gbRatRecon.m2"

export {
    -- Support routines
    radicalContainment, -- test
    factors, -- test
    findNonMemberIndex, -- test
    toAmbientField, -- make as a string so that we dont have to export?
    fromAmbientField,  -- make as a string so that we dont have to export?
    -- Main functions
    minprimes
    }

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
    null
    )

--------------------------------
-- Factorization ---------------
--------------------------------
-- setAmbientField:
--   input: KR, a ring of the form kk(t)[u] (t and u sets of variables)
--          RU, kk[u,t] (with some monomial ordering)
--   consequence: sets information in KR so that
--     'factors' and 'numerator', 'denominator' work for elemnts of KR 
--     sets KR.toAmbientField, KR.fromAmbientField
setAmbientField = method()
setAmbientField(Ring, Ring) := (KR, RU) -> (
    -- KR should be of the form kk(t)[u]
    -- RU should be kk[u, t], with some monomial ordering
    KR.toAmbientField = map(frac RU,KR);
    KR.fromAmbientField = (f) -> (if ring f === frac RU then f = numerator f; (map(KR,RU)) f);
    numerator KR := (f) -> numerator KR.toAmbientField f;
    denominator KR := (f) -> denominator KR.toAmbientField f;
    )

-- needs documentation
factors = method()
factors RingElement := (F) -> (
    R := ring F;
    if F == 0 then return {(1,F)};
    facs := if R.?toAmbientField then (
        F = R.toAmbientField F;
        numerator factor F
        )
    else if isPolynomialRing R and instance(coefficientRing R, FractionField) then (
        KK := coefficientRing R;
        A := last KK.baseRings;
        RU := (coefficientRing A) (monoid[generators R, generators KK, MonomialOrder=>Lex]);
        setAmbientField(R, RU);
        F = R.toAmbientField F;
        numerator factor F
        )
    else if instance(R, FractionField) then (
        -- What to return in this case?
        -- WORKING ON THIS MES
        error "still need to handle FractionField case";
        )
    else factor F;
    facs = apply(#facs, i -> (facs#i#1, (1/leadCoefficient facs#i#0) * facs#i#0 ));
    facs = select(facs, (n,f) -> # support f =!= 0);
    if R.?toAmbientField then apply(facs, (r,g) -> (r, R.fromAmbientField g)) else facs
    )

findElementThatFactors = method()
findElementThatFactors List := L -> (
    -- sort L by number of terms first?
    for f in L do (
      -- don't try to factor a large polynomial?
      facs := factors f;
      if #facs > 1 or (#facs == 1 and facs#0#0 > 1) then return (f,facs/last);
    );
    (null, {})
    )

-- this code was taken from FactorizingGB.m2
facGB0 = method(Options => {"UseColon"=>true})
facGB0(Ideal, Set) := opts -> (I, nonzeros) -> (
    -- returns a pair (P:List, L:List)
    --  where : P is a list of ideals, that have no factorization left.
    --  and     L is a list of (J:ideal, nonz: nonzeros), 
    --  where J is an ideal containing I, and nonz is a set of monic polynomials, which 
    --  are not in the resulting min primes
    (f, facs) := findElementThatFactors I_*; -- chooses a generator of I that factors
    if #facs == 0 then ( 
        --<< "no elements found that factor" << endl; << "ideal is " << toString I << endl; 
        return ((I, nonzeros), {})
        );
    prev := set{};
    nonzeroFacs := toList(set facs - nonzeros);
    L := for g in nonzeroFacs list (
          --if member(g, nonzeros) then continue;
          -- colon or sum?
          J := null;
          if opts#"UseColon" then (
             -- TODO: Find the components that are missing when using colons!
             J = saturate(I, f // g);
             I = (I : J);
          )
          else (
             J = (ideal(g) + I);
             J = trim ideal apply(J_*, f -> (
                 product toList (set ((factors f)/last) - nonzeros)
             ));
          );
          result := (J, nonzeros + prev);
          prev = prev + set{g};
          if numgens J === 1 and J_0 == 1 then continue else result
    );
    ({}, L)
)

facGB = method(Options=>{Limit=>infinity, "UseColon"=>true})
facGB Ideal := opts -> (J) -> (
    C := {};
    L := {(J,set{})};
    i := 0;
    while i < opts.Limit and #L > 0 do (
        L2 := flatten for j in L list (
            (C1,L1) := facGB0(j,"UseColon"=>opts#"UseColon");
            if C1 =!= {} then C = append(C, C1);
            L1
        );
        L = L2;
        << "number: " << (i, #C, #L) << endl;
        --<< "C = " << netList C << endl;
        --<< "L = " << netList L << endl;
        i = i+1;
    );
    (C, L)     
)

-----------------------------
-- Redundancy control -------
-----------------------------
-- find, if any, an element of I which is NOT in the ideal J.
-- returns the index x of that element, if any, else returns -1.
raw  = value Core#"private dictionary"#"raw"
rawGBContains = value Core#"private dictionary"#"rawGBContains"
findNonMemberIndex = method()
findNonMemberIndex(Ideal,Ideal) := (I,J) -> (
     m := generators I;
     n := gb J;
     rawGBContains(raw n, raw m)
     )

-- The following function removes any elements which are larger than another one.
-- Each should be tagged with its codimension.  For each pair (L_i, L_j), check containment of GB's
selectMinimalIdeals = (L) -> (
    L = L/(i -> (codim i, flatten entries gens gb i))//sort/last/ideal;
    ML := new MutableList from L;
    for i from 0 to #ML-1 list (
        if ML#i === null then continue;
        for j from i+1 to #ML-1 do (
            if ML#j === null then continue;
            if findNonMemberIndex(ML#i, ML#j) === -1 then ML#j = null;
            );
        ML#i
        )
    )

makeFiberRings = method()
makeFiberRings(List) := (baseVars) -> (
   -- This function takes an ideal I and a list of variables baseVars as input
   -- and returns a pair of matrices (mons, cs) where mons are the monomials in the ideal
   -- of lead terms of a gb of I, and cs are the coefficients, but with respect to
   -- a product order kk[fiberVars][baseVars].  See tests for behavior
   if #baseVars == 0 then error "expected at least one variable in the base";
   R := ring baseVars#0;
   if any(baseVars, x -> ring x =!= R) then error "expected all base variables to have the same ring";
   allVars := set gens R;
   fiberVars := rsort toList(allVars - set baseVars);
   baseVars = rsort baseVars;
   S := (coefficientRing R) monoid([fiberVars,baseVars,MonomialOrder=>Lex]);
       --MonomialOrder=>{#fiberVars,#baseVars}]);
   KK := frac((coefficientRing R)(monoid [baseVars]));
   SF := KK (monoid[fiberVars, MonomialOrder=>Lex]);
   S#cache = new CacheTable;
   S.cache#"StoSF" = map(SF,S,sub(vars S,SF));
   S.cache#"SFtoS" = map(S,SF,sub(vars SF,S));
   S.cache#"StoR" = map(R,S,sub(vars S,R));
   S.cache#"RtoS" = map(S,R,sub(vars R,S));
   setAmbientField(SF, S);
   (S, SF)
   )

minimalizeOverFrac = method()
minimalizeOverFrac(Ideal, Ring) := (I, SF) -> (
     -- Input:  I is an ideal in a ring with an elimination order (maybe Lex)
     --         SF is of the form k(basevars)[fibervars].
     --         If G is a GB of I, then G SF is a GB if I S.
     -- Output: A reduced minimal Groebner basis of I SF, as a list
     --         of polynomials (defined over SF).
     -- Caveat: ring I must have either a lex order or a product order, compatible with
     --  fibervars >> basevars, and must have been created with makeFiberRings
     S := ring I;
     G := flatten entries gens gb I;
     phi := S.cache#"StoSF";
     psi := map(S,SF);
     sz := G/size; -- number of monomials per poly, used to choose which elem to take
     GS := flatten entries phi gens gb I;
     minG := flatten entries mingens ideal(GS/leadMonomial);
     GF := for mon in minG list (
        z := positions(GS, f -> leadMonomial f == mon);
        i := minPosition (sz_z);
        GS_(z#i)
     );
     -- QUESTION : Do we really wany 'numerator' here instead of psi?
     coeffs := GF/leadCoefficient/psi;
     (flatten entries gens forceGB matrix(SF,{GF}), coeffs)
     )

-- Question: What if we want to contract away only some of the basevars, not all of them?  Will this ever
--           be the case?
-- TODO NOTE: the saturate here should be done in the ring R (grevlex)
contractToPolynomialRing = method(Options => {Verbosity => 0})
contractToPolynomialRing(Ideal) := opts -> (I) -> (
     -- assumes: I is in a ring k(basevars)[fibervars] created with makeFiberRings
     -- returns the intersection of I with k[fibervars,basevars] (also created with makeFiberRing).
     --   note: numerator (and denominator) of element in ring I gives an element in k[fibervars,basevars]
     if not instance(coefficientRing ring I, FractionField) then return I; -- in this case, we are already contracted!
     newI := I_*/numerator//ideal//trim;
     S := ring newI;
     denoms := I_*/denominator;
     denomList := unique flatten for d in denoms list (factors d)/last;
     if opts.Verbosity > 0 then << "denoms = " << denoms << " and denomList = " << denomList << endl;
     Isat := S.cache#"StoR" newI;
     for f in denomList do Isat = saturate(Isat, S.cache#"StoR" f);
     S.cache#"RtoS" Isat
     )

extendIdeal = method()
extendIdeal Ideal := (I) -> (
     -- I is an ideal
     -- returns an ideal whose elements are a reduced GB of I k(indepset)[fibervars]
     indep := support first independentSets(I, Limit=>1);
     (S,SF) := makeFiberRings indep;
     IS := S.cache#"RtoS" I;
     time gens gb IS;
     (JSF, coeffs) := minimalizeOverFrac(IS, SF);
     ideal JSF
     )

squarefreeGenerators = method()
squarefreeGenerators (ZZ,Ideal) := (n,I) -> (
   madeChanges := false;
   J := ideal for g in I_* list (
              if size g > n then g
              else (
                gfacs := factors g;
                if #gfacs > 1 or gfacs#0#0 > 1 then (
                  madeChanges = true;
                  gfacs / last // product
                )
                else g
              )
              );
   if madeChanges then J else I
)
-----------------------
-- Minimal primes -----
-- 25 Sep 2012: Frank+Franzi+Mike working on this
-----------------------
minprimes = method(Options => {
        Verbosity => 0,
        "SquarefreeFactorSize" => 1,
        Ideal => null,  -- used in inductive setting
        "RadicalSoFar" => null -- used in inductive setting
        })
minprimes Ideal := opts -> (I) -> (
    -- possibly do some preprocessing (exactly what to do here requires work
    -- and a separate function)
    -- returns a list of ideals, the minimal primes of I
    R := ring I;
    --- pre-processing of ideals
    J := squarefreeGenerators(opts#"SquarefreeFactorSize",I);
    phi := identity;
    doSimplifyIdeal := any(gens R, x -> any(I_*, f -> first degree diff(x,f) == 0));
    if doSimplifyIdeal then (J,phi) = simplifyIdeal I;
    --- compute minimal primes of the processed ideals
    C := minprimesWorker(J, opts);
    C1 := C / (c -> contractToPolynomialRing(c,Verbosity=>opts.Verbosity));
    C2 := C1 / (i -> (ring i).cache#"StoR" i);
    --- post-processing of ideals
    (selectMinimalIdeals C2) / phi
    )

minprimesWorker = method (Options => options minprimes)
minprimesWorker Ideal := opts -> (I) -> (
    R := ring I;
    radicalSoFar := ideal 1_R;
    comps := {};
    J := I;
    loopCount := 1;
    while J != 1 do (
        if opts.Verbosity > 0 then 
          << "-- handling " << toString J << endl;
        (I1set, I2) := equidimSplitOneStep(J, opts);
        (I1, basevars, ISF) := I1set;
        --D := splitPurePowers ideal ISF;
        D := splitLexGB ideal ISF;
        --comps = join(comps, (apply(D, j -> splitTower(j,opts))) // flatten); -- old splitTower
        -- is there a way to use the polyCRA trick in nonzero characteristic?
        if char ring I != 0 then comps = join(comps, (apply(D, j -> splitTower(j,opts))) // flatten)
          else comps = join(comps, (apply(D, j -> factorIrredZeroDimensionalTower(j,Verbosity=>opts.Verbosity))) // flatten);
        J = I2;
        loopCount = loopCount + 1;
        );
    comps
    )

equidimSplitOneStep = method(Options => options minprimes)
equidimSplitOneStep Ideal := opts -> (I) -> (
    -- return ((I1: equidim ideal, basevars, ISF), I2)
    -- where 1. intersection of I1 and I2 is I
    --       1. ISF = minimal GB of I1 kk(basevars)[fibervars]
    --       2. I1 is equidimensional (zero dim over kk(basevars))
    --          and so I1 is the contraction of ideal ISF to R
    --       3. I2 is I:I1.  Note:
    --          radical(intersection(I1,I2)) = intersection(radical(I1),radical(I2))
    if I == 1 then error "Internal error: Input should not be unit ideal.";
    R := ring I;
    indeps := independentSets(I, Limit=>1);
    basevars := support first indeps;
    if opts.Verbosity > 0 then 
        << "  Choosing: " << basevars << endl;
    -- COMMENT FROM FRANK: I feel like we should do the below in a similar manner to the
    --                     general case, and allow makeFiberRings to handle empty basevars.
    if #basevars == 0 then (
        Slex := newRing(R, MonomialOrder=>Lex);
        Slex#cache = new CacheTable;
        Slex.cache#"RtoS" = map(Slex,R,sub(vars R,Slex));
        Slex.cache#"StoR" = map(R,Slex,sub(vars Slex,R));
        Slex.cache#"StoSF" = identity;
        Slex.cache#"SFtoS" = identity;
        numerator Slex := identity;
        ISlex := Slex.cache#"RtoS" I;
        return ((I, {}, (ideal gens gb ISlex)_*), ideal 1_R);
        );
    (S, SF) := makeFiberRings basevars;
    IS := S.cache#"RtoS" I;
    gens gb IS;
    (ISF, coeffs) := minimalizeOverFrac(IS, SF);
    if coeffs == {} then ((I,basevars,ISF),ideal {1_R}) else (
       facs := (factors product coeffs)/last;
       G := product facs;
       if opts.Verbosity > 0 then
           << "  the factors of the flattener: " << netList(facs) << endl;
       G = S.cache#"StoR" G;
       I1 := saturate(I, G);
       I2 := trim (I : I1);
       ((I1, basevars, ISF), I2)
    ))

-----------------------
-- Splitting methods --
-----------------------

-- Below, IF is a reduced lex GB for I k(indep)[fiber]
-- This function factors the terms that are not linear in a GB for IF and splits the ideal by those factors
-- This function returns the empty list if I is the unit ideal.
splitLexGB = method()
splitLexGB Ideal := (IF) -> (
    L := IF_*;
    for f in L do (
        facs := factors f;
        if #facs == 1 and facs#0#0 == 1 then continue;
        return flatten for fac in facs list splitLexGB (ideal gens gb ((ideal fac#1) + IF));
        );
    {IF}
    )

-- This function determines whether or not the lead term of the input polynomial is linear
hasLinearLeadTerm = method()
hasLinearLeadTerm RingElement := (f) -> (
    t := leadTerm f;
    s := support t;
    #s === 1 and s#0 == t
    )

splitTower = method(Options => options minprimes)
splitTower Ideal := opts -> (IF) -> (
    -- IF is an ideal in k(basevars)[fibervars] satisfying:
    --   1. IF is zero-dimensional
    --   2. IF_* is a lex GB for IF (in ascending order of leadterms)
    --   3. IF_* only contains (hopefully!) elements whose lead term is a pure power.
    --   4. each element IF_i is irreducible over the fraction field k(basevars).
    -- Output: a list of ideals, each one should be a minimal prime of IF.
    E := partition(hasLinearLeadTerm, IF_*);
    if not E#?false then return {IF}; -- nothing to do
    nonlinears := E#false;
    if #nonlinears <= 1 then return {IF};
    SF := ring IF;
    linears := if E#?true then E#true else {}; -- keep for later
    J := ideal nonlinears;
    vecdim := nonlinears/leadTerm/(f -> first degree f)//product;
    L := ideal (J_* / numerator);
    S := ring L;
    varsList := nonlinears / leadTerm / support // flatten;
    lastVar := varsList#0; -- this is the smallest variable in the monomial order
    otherVars := drop(varsList, 1); 
    F := sum apply(otherVars, x -> (1 + random 10) * x);
    J1 := sub(J, lastVar => lastVar + F);
    L1 := ideal(J1_*/numerator);
    lastVar = numerator lastVar;
    otherVars = otherVars/numerator;
    G := (eliminate(L1, otherVars))_0;
    completelySplit := degree(lastVar, G) === vecdim;
    facs := factors G;
    if opts.Verbosity > 0 then print netList facs;
    F = numerator F;
    facs1 := apply(facs, (mult,h) -> (mult,sub(h, lastVar => lastVar - F)));
    if #facs1 == 1 and facs1#0#0 == 1 then {IF}
    else flatten for fac in facs1 list (
        G := fac#1 % L;
        C := time ideal gens gb(ideal S.cache#"StoSF" G + J);
        if C == 1 then continue;
        --time C := ideal first minimalizeOverFrac((ideal G) + L, SF);
        P := ideal gens gb (C + ideal linears);
        if completelySplit then P else flatten splitTower P
        )
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


beginDocumentation()

doc ///
Key
  PD
Headline
  Primary Decomposition
Description
  Text
    Describe the package here.
  Example
Caveat
SeeAlso
///

end

restart
loadPackage "PD"

----------------------------------------------------------------------------
-- code below here is not needed for most recent implementation of minprimes
----------------------------------------------------------------------------

{* -- the next two functions were just MES playing around.
   -- they should probably be ignored or removed.
   
minprimes Ideal := opts -> (I) -> (
    -- this is the top level function
    -- 1. Check ring of I to see if it can be handled
    -- 2. Flatten the ring
    -- 3. if I is a CI, flag this info, to call minprimesEquidim
    -- 4. if I has polynomials with linear parts, try to split using 
    --    simplifyIdeal
    -- 4a. if I is a monomial ideal, call specialized code for that
    -- 5. possibly replace each f with its square-free part
    -- 5. possibly do some factorization first
    --    one way: if fg \in I, then I1 = saturate(I, f), I2 = I:I1, continue.
    R := ring I;
    ans := minprimes0(I, "RadicalSoFar" => ideal(1_R), Ideal => I, Verbosity => opts.Verbosity);
    (resultComponents, newRadSoFar) := ans;
    -- resultComponents should be a list of prime ideals
    -- if ring had changed, map everything back
    resultComponents
    )


minprimes0 = method (Options => options minprimes)
minprimes0 Ideal := opts -> (I) -> (
    -- I should be in a nice ring, e.g. a grevlex order ring.  We assume that this is the ring
    -- in which we should compute saturations, ideal quotients, intersections.
    indeps := independentSets(I, Limit=>1);
    basevars := support first indeps;
    if opts.Verbosity > 0 then 
        << "  Choosing: " << basevars << endl;
    (comps, newRadSoFar, reallyDone) :=  minprimesZeroDim(I, basevars, opts);
    if reallyDone then return (comps, newRadSoFar);
    -- If not done yet, then what?
    -- need saturate(I, something).
    --I1 := saturate(I, something);
    --I2 := I : I1;
    --comps2 := minprimes0(I2, "RadicalSoFar" => newRadSoFar, Ideal => opts.
    comps2 := {};
    selectMinimalIdeals join(comps, comps2)
    )
*} -- see beginning of comment, two functions above.

minprimesZeroDim = method (Options => options minprimes)
minprimesZeroDim(Ideal, List) := opts -> (I, basevars) -> (
    -- I is an ideal in R, basevars is a list of variables of R
    -- computes the list of minimal primes of I which dominate basevars.
    --  except: minimal primes larger than opts#"RadicalSoFar" are thrown out
    -- Also: if we obtain a set of prime ideals such that
    --  intersection of these ideals with opts#"RadicalSoFar"
    --  is equal to opts.Ideal, then we are "really done".
    -- reallyDoneFlag is false, if not all components of original ideal opts.Ideal have been found.
    -- return value: 
    --  (list of primes found,  intersection of these primes with opts#"RadicalSoFar", reallyDoneFlag)
    (S, SF) := makeFiberRings basevars;
    IS := sub(I, S);
    gens gb IS;
    (ISF, coeffs) := minimalizeOverFrac(IS, SF);
    G := (factors product coeffs)/last//product;
    << "  the factors of the flattener: " << netList((factors G)/last) << endl;
    G = sub(G,ring I);
    I1 := saturate(I, G);
    error "debug me";
    )

equidimSplit = method(Options => options minprimes)
equidimSplit Ideal := opts -> (I) -> (
    (L1, I2) := equidimSplitOneStep(I, opts);
    if I2 == 1
    then {L1} 
    else prepend(L1, equidimSplit(I2, opts))
    )

TEST ///
    restart
    debug loadPackage "PD"
    load "PD/example-adjacentminors.m2"
    I = adjacentMinorsIdeal(2,3,3,CoefficientRing=>ZZ/32003)
    comps = {ideal(-b*d+a*e,-c*e+b*f,-c*d+a*f,-e*g+d*h,-b*g+a*h,-f*h+e*i,-f*g+d*i,-c*h+b*i,-c*g+a*i), 
        ideal(e,b,h), 
        ideal(e,d,f)}; -- from 'decompose'
    C = equidimSplit(I, Verbosity=>10)
    C1 = drop(C, -1)
    -- It just so happens that the ideals returned by equidimSplit in this example
    -- are already prime.
    assert(
        set(C1/first/(g -> flatten entries gens gb g)) === 
        set(comps/(g -> flatten entries gens gb g))
        )
///

TEST ///
    restart
    debug loadPackage "PD"
    R = ZZ/32003[a,b,c,h]
    I = ideal(a+b+c,a*b+b*c+a*c,a*b*c-h^3)
    minprimesWorker(I, Verbosity=>1)
    C = equidimSplit(I, Verbosity=>10)
///

splitBy = (I, h) -> (
     Isat := saturate(I, h);
     f := 1_(ring I);
     while not isSubset(f*Isat, I) do f = f*h;
     if Isat == I or Isat == 1 then error ("alas, your element "|toString h|" is not a splitting element");
     if f == 1 then null else (Isat, trim(I + ideal f))
     )
-- Needs test

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
-- Needs test

-- documentation needed
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
     J2 := I : J1;
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
-- Needs test

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
-- needs test
hasLinearLeadTerm = method()
hasLinearLeadTerm RingElement := (f) -> (
    t := leadTerm f;
    s := support t;
    #s === 1 and s#0 == t
    )

findPurePowers = method()
findPurePowers Ideal := (IF) -> (
     -- IF is a reduced lex GB for I k(indep)[fiber]
     -- returns the list of n (= #fiber) polynomials, s.t. i-th one has lead term x_i^(a_i),
     --   where x_i are the fiber variables
     select(IF_*, f -> # support leadTerm f == 1)
     )

findNonlinearPurePowers = method()
findNonlinearPurePowers Ideal := (IF) -> (
     -- IF is a reduced lex GB for I k(indep)[fiber]
     -- returns the list of n (= #fiber) polynomials, s.t. i-th one has lead term x_i^(a_i),
     --   where x_i are the fiber variables, and a_i > 1
     select(IF_*, f -> (
         t := leadTerm f;
         s := support t;
         #s === 1 and s#0 != t))
     )

-- Below, IF is a reduced lex GB for I k(indep)[fiber]
-- This function factors the terms that are not linear in a GB for IF and splits the ideal by those factors
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

-- Below, IF is a reduced lex GB for I k(indep)[fiber]
-- In this function, the polynomials themselves are irreducible over the field if not considered as a whole,
-- but one can see some linear terms that split if we change coordinates.
-- A good example is if the ideal (over QQ) has r^2-3 and x^2-3y^2 in it.  This should
-- split as r^2-3,x+ry and r^2-3, x-ry.
purePowerCoordinateChange = method()
purePowerCoordinateChange Ideal := (IF) -> (
    purePowers := findNonlinearPurePowers IF;
    otherGens := toList((set IF_*) - (set purePowers));
    J := ideal purePowers;
    L := ideal (J_* / numerator);
    varsList := purePowers / leadTerm / support // flatten;
    F := sum apply(drop(varsList,1), x -> (1 + random 10) * x);
    J1 := sub(J, varsList#0 => varsList#0 + F);
    L1 := ideal(J1_*/numerator);
    varsList = apply(varsList, f -> sub(f, ring L1));
    time facs := factors (eliminate(L1, drop(varsList,1)))_0;
    F = sub(F,ring L1);
    time facs1 := apply(facs, (mult,h) -> (mult,sub(h, varsList#0 => varsList#0 - F)));
    if #facs1 == 1 and facs1#0#0 == 1 then {IF}
    else for fac in facs1 list (
        time G := fac#1 % L;
        time C := ideal first minimalizeOverFrac((ideal G) + L, ring J);
        time ideal gens gb (C + ideal otherGens)
        )
    )
TEST ///
  restart
  debug loadPackage "PD"

  -- this example is one step from the stewart-gough example  
  R = QQ[e_1, e_2, e_3, e_4, g_1, g_2, g_3, g_4, r]
  J = ideal(r^2-3,
       g_3*r+e_1,
       e_1*r+3*g_3,
       e_4*g_3-e_3*g_4,
       g_2^2-3*g_3^2,
       e_3*g_2-e_2*g_3,
       e_2*g_2-3*e_3*g_3,
       e_1*g_1+4*e_3*g_3+e_4*g_4,
       2*e_4^2+9*g_1^2+24*g_3^2+9*g_4^2,
       4*e_3^2-3*g_1^2-6*g_3^2-3*g_4^2,
       4*e_2^2-9*g_1^2-18*g_3^2-9*g_4^2,
       e_1^2-3*g_3^2,
       e_4*g_2*r-e_2*g_4*r,
       g_1^2*r+g_4^2*r+2*e_3*g_1-4*e_1*g_3,
       e_4*g_1*r+2*e_3*e_4+3*g_3*g_4,
       2*e_3*g_1*r+3*g_1^2+12*g_3^2+3*g_4^2,
       2*e_3*e_4*r+3*e_4*g_1-3*e_1*g_4,
       2*e_2*e_3*r+3*e_2*g_1-3*e_1*g_2,
       6*e_3*g_1*g_3-4*e_1*g_3^2+e_4*g_1*g_4-e_1*g_4^2,
       6*e_2*e_3*g_3+3*g_2*g_3^2+e_2*e_4*g_4,
       e_1*e_4*g_2-e_1*e_2*g_4,
       2*e_1*e_3*e_4-3*e_3*g_1*g_4+3*e_1*g_3*g_4,
       2*e_1*e_2*e_4-3*e_2*g_1*g_4+3*e_1*g_2*g_4,
       2*e_1*e_2*e_3-3*e_2*g_1*g_3+3*e_1*g_2*g_3)
  JE = extendIdeal J
  
  findNonlinearPurePowers JE
  gbTrace = 3
  newJEs = purePowerCoordinateChange JE
///

-------------------------------------
-- Factorization over a tower -------
-------------------------------------

factorOverTower = method()
factorOverTower(RingElement, List) := (F, L) -> (
    -- factor F over the field extension defined by L
    -- input: F, a polynomial in a ring k(basevars)[fibervars]
    --        L, a list of polynomials, such that L_i has lead term a pure power of a variable
    --           and this lead term is not a variable
    --           and L is sorted in decreasing variable index
    --           and L defines a finite field extension of k(basevars).
    --        the only variables in 'fibervars' that occur in F should be the lead term variables of L,
    --           and one other 'x' (which is the support of the lead monomial of F).
    -- output: a list of (d_i, F_i), such that
    --   F_i is monic in x,
    --   F = product F_i ^ d_i
    --   each F_i is irreducible over L
    )

-- experimental: not functional
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
-- needs test
