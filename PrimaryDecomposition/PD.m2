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

exportMutable {MONICTOWERTRICK} --- remove this, debugging only

export {
    -- Support routines
    radicalContainment, -- test
    factors, -- test
    findNonMemberIndex, -- test
    toAmbientField, -- make as a string so that we dont have to export?
    fromAmbientField,  -- make as a string so that we dont have to export?
    -- Main functions
    minprimes,
    minprimesWithStrategy,
    splitIdeal,
    splitIdeals,
    AnnotatedIdeal,
    Linears,
    NonzeroDivisors,
    Inverted,
    FiberInfo,
    LexGBOverBase,
    nzds,
    Birational,  -- Strategy option for splitIdeal.  Exported now for simplicity
    IndependentSet,
    SplitTower,
    LexGBSplit,
    Factorization,
    DecomposeMonomials,
    Trim,
    CharacteristicSets,
    Minprimes,
    Squarefree
    }
MONICTOWERTRICK = true
strat0 = ({Linear,DecomposeMonomials},infinity)
strat1 = ({Linear,DecomposeMonomials,(Factorization,3)},infinity)
Birational = ({strat1, (Birational,infinity)},infinity)
NoBirational = strat1
minprimes = method(Options => {
        Verbosity => 0,
        Strategy => Birational,  -- if null, calls older minprimesWorker code
        "SquarefreeFactorSize" => 1,
        "CodimensionLimit" => null, -- only find minimal primes of codim <= this bound
        "IdealSoFar" => null,  -- used in inductive setting
        "RadicalSoFar" => null -- used in inductive setting
        })

load (PD#"source directory"|"PD/annotated-ideals.m2")
--load (PD#"source directory"|"PD/oldMinPrimes.m2")

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
-- and null, if none
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

-----------------------------
-- Birational reduction -----
-----------------------------
removeNull = (L) -> select(L, x -> x =!= null)
makeLinearElement = (x,f) -> (
    -- x is a variable
    -- f is a polynomial
    -- returns null if f is not linear as a polynomial in x
    -- otherwise returns
    -- (x, g, f1),
    --    where f1 = xg-h, 
    --   g and h do not involve x, and g is monic
    g := contract(x,f);
    if g == 0 then return null;
    if contract(x,g) != 0 then return null;
    c := leadCoefficient g;
    f = 1/c * f;
    g = 1/c * g;
    --h := x*g-f;
    (x, g, f)
    )
replaceVariable = (I, m) -> (
    -- reduce by x-p, p doesn't involve x, but x might not be the lead term of x-p.
    if leadTerm m#2 === m#0
    then ideal compress ((gens I) % m#2)
    else ideal compress sub(gens I, m#0 => m#0 * m#1 - m#2)
    )
eliminateLinear = (I, m) -> (
    -- I is an ideal
    -- m is a list as returned by makeLinearElement
    -- returns the ideal with I eliminated
    if m#1 == 1 
    then replaceVariable(I,m)
    else eliminate(I, m#0)
    )
linears = (x,I) -> I_* / (F -> makeLinearElement(x,F)) // removeNull
findBirationalPoly = (x,I) -> (
    M := linears(x,I);
    if #M === 0 then null
    else (
        M1 := sort apply(M, m -> (size m#1, first degree m#1, m));
        last first M1
        )
    )
findGoodBirationalPoly = (I) -> (
    -- given an ideal I, returns either null or a tuple (x, g, f)
    -- (see makeLinearElement for a description of these items)
    M := removeNull for x in gens ring I list (
        findBirationalPoly(x,I)
        );
    M = sort apply(M, m -> (size m#1, first degree m#1, m));
    if #M === 0 then null else last first M
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
makeFiberRings List := basevars -> if #basevars == 0 then error "Expected at least one variable in the base" else makeFiberRings(basevars,ring (basevars#0))
makeFiberRings(List,Ring) := (basevars,R) -> (
   -- This function takes a (possibly empty) list of variables basevars as input
   -- and returns a pair of matrices (mons, cs) where mons are the monomials in the ideal
   -- of lead terms of a gb of I, and cs are the coefficients, but with respect to
   -- a product order kk[fiberVars][basevars].  See tests for behavior
   -- If basevars does happen to be empty, then the original ring with Lex order is returned.
   local S;
   if #basevars == 0 then (
        -- in this case, we are not inverting any variables.  So, S = SF, and S just has the lex
        -- order.
        S = newRing(R, MonomialOrder=>Lex);
        S#cache = new CacheTable;
        S.cache#"RtoS" = map(S,R,sub(vars R,S));
        S.cache#"StoR" = map(R,S,sub(vars S,R));
        S.cache#"StoSF" = identity;
        S.cache#"SFtoS" = identity;
        numerator S := identity;
        (S,S)
   )
   else
   (
      if any(basevars, x -> ring x =!= R) then error "expected all base variables to have the same ring";
      allVars := set gens R;
      fiberVars := rsort toList(allVars - set basevars);
      basevars = rsort basevars;
      S = (coefficientRing R) monoid([fiberVars,basevars,MonomialOrder=>Lex]);
          --MonomialOrder=>{#fiberVars,#basevars}]);
      KK := frac((coefficientRing R)(monoid [basevars]));
      SF := KK (monoid[fiberVars, MonomialOrder=>Lex]);
      S#cache = new CacheTable;
      S.cache#"StoSF" = map(SF,S,sub(vars S,SF));
      S.cache#"SFtoS" = map(S,SF,sub(vars SF,S));
      S.cache#"StoR" = map(R,S,sub(vars S,R));
      S.cache#"RtoS" = map(S,R,sub(vars R,S));
      setAmbientField(SF, S);
      (S, SF)
   )
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
     psi := S.cache#"SFtoS";
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

-- This function determines whether or not the lead term of the input polynomial is linear
hasLinearLeadTerm = method()
hasLinearLeadTerm RingElement := (f) -> (
    t := leadTerm f;
    s := support t;
    #s === 1 and s#0 == t
    )

-------------------------------------------------------------
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

