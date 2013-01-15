-- part of PD.m2, uses code from there too

AnnotatedIdeal = new Type of MutableHashTable
-- fields of this type:
--  A.Ideal
--  A.Linears
--  A.Inverted
--  A.NonzeroDivisors
------- IndependentSet Flags : The existence of the following two flags also implies the
-------                        ideal is equidimensional
--  A.IndependentSet   This is a triple (basevars,S,SF) where S,SF are returned from makeFiberRings
--  A.LexGBOverBase  GB of ISF over SF
-- Finished Flags: if any of these flags exists, then that split
-- technique is done on that ideal.
--  A.Birational   
--  A.Linear
--  A.Factorization
--  A.Squarefree
--  A.IndependentSet

-- An "annotated ideal" is a tuple (I, L, NZ, inverteds)
-- where I is an ideal (in a subset of the variables)
-- L is a list of (x, g, f), where 
--   x is a variable (not appearing in I at all)
--   g is a poly not involving x
--     g is  monic
--   f = xg-h is in the original ideal (leadTerm f is not nec leadTerm(xg))
-- NZ: list of known nonzero-divisors *need more detail here of how they are used*
-- inverteds: Elements that have been 'inverted' in the calculation.  Need to saturate
--  with respect to these when using ideal AnnotatedIdeal.
-- This ideal represents I', where
-- I' = saturate(I + ideal (L/last), product of L/(s -> s#1)).

monicUniqueFactors = polyList -> (
    polyList1 := polyList/factors//flatten;
    polyList2 := select(polyList1, g -> #g > 0);
    polyList2 / last // unique
)

annotatedIdeal = method()
annotatedIdeal(Ideal, List, List, List) := (I, linears, nzds, inverted) -> (
    -- I is an ideal
    -- linears is a list of LinearElement's (x, g, f), where 
    --   f = xg-h is in the ideal, 
    --   g and h don't involve x
    --   and g is monic over the base field
    -- nzds is a list of polynomials which are nzds's of the associated ideal
    -- inverted is a list of elements such that we ignore the minimal primes
    --   that contain any of these elements
    -- The associated ideal is:
    --   saturate(I + ideal(linears/last), product unique join((linears / (x -> x#1)),inverted))
    new AnnotatedIdeal from {
        symbol Ideal => I, 
        symbol Linears => linears, 
        symbol NonzeroDivisors => monicUniqueFactors nzds,
        symbol Inverted => monicUniqueFactors inverted
        }
    )

annotatedIdeal Ideal := (I) -> (
     -- input: ideal I in a polynomial ring R
     linears := for x in gens ring I list (
         k := position(I_*, f -> first degree contract(x,f) == 0);
         if k === null then continue;
         m := makeLinearElement(x, I_k);
         I = replaceVariable(I,m);
         m);
     newI := annotatedIdeal(I, linears, {}, {});
     if #linears === 0 then newI.Linear = true;
     newI
     )

net AnnotatedIdeal := (I) -> (
    net new HashTable from {
        "Ideal" => if numgens I.Ideal === 0 then net I.Ideal else netList (I.Ideal)_*, 
        "Linears" => netList (I.Linears)}
    )

ring AnnotatedIdeal := (I) -> ring I.Ideal

ideal AnnotatedIdeal := (I) -> (
    --F := product I.NonzeroDivisors;
    F := product unique join(I.Linears / (x -> x#1),I.Inverted);
    I1 := ideal(I.Linears/last);
    I2 := I.Ideal;
    I3 := if numgens I1 === 0 then I2 else if numgens I2 === 0 then I1 else I1+I2;
    if F == 1 then I3 else saturate(I3, F)
    )

isPrime AnnotatedIdeal := (I) -> (
    if not I.?isPrime or I.isPrime === "UNKNOWN" then (
        I.isPrime = if numgens I.Ideal == 0 then "YES" else
                    if I.?Factorization and numgens I.Ideal == 1 then "YES" else
                    "UNKNOWN";
       );
    I.isPrime
    )

partitionPrimes = method()
partitionPrimes List := Is -> (
   P := partition(I -> isPrime I === "YES",Is);
   -- have to check to see if there are any true/false at all before '#'
   (if P#?true then P#true else {},if P#?false then P#false else {})
)

partitionPrimes AnnotatedIdeal := I -> partitionPrimes {I}

flagIsPrime = method()
flagIsPrime AnnotatedIdeal := I -> (isPrime I; I)

--- this is so that we can add in generators to I and keep track of
--- how the annotation changes
AnnotatedIdeal + Ideal := (I,J) -> (
   annotatedIdeal(J + I.Ideal,
                  I.Linears,  -- 'linear' generators
                  {},        -- clear out nonzerodivisor list
                  unique join(I.NonzeroDivisors,I.Inverted)) -- move nonzerodivisors to inverted list
)

trim AnnotatedIdeal := opts -> I -> (
    I.Ideal = trim I.Ideal;
    I
)

squarefreeGenerators AnnotatedIdeal := opts -> I -> (
   if I.?Squarefree then return I; 
   nonzeros := set I.Inverted;
   J := I.Ideal;
   n := opts#"SquarefreeFactorSize";
   madeChanges := false;
   J1 := ideal for g in J_* list (
              if size g > n then g
              else (
                nonzeroFacs := set ((factors g) / last) - nonzeros;
                h := product toList nonzeroFacs;
                if g != h then madeChanges = true;
                h
              )
         );
   if madeChanges then
      -- note that the NonzeroDivisor list is empty below since elements
      -- can become zerodivisors when removing powers of generators
      annotatedIdeal(J1,I.Linears,{},unique join(I.NonzeroDivisors,I.Inverted))
   else 
      I
)

nzds = method()
nzds AnnotatedIdeal := (I) -> I.NonzeroDivisors
------------------------------------------------------------
-- splitIdeal code
splitIdeal = method(Options => {Strategy=>null,
                                Verbosity=>1,
                                "SquarefreeFactorSize" => 1})
  -- possible Strategy values:
  --  Linear     -- Eliminates variables where a generator is of the form x - g
                 -- for g not containing x
  --  Birational         -- Tries to eliminates variables where a generator is of
                         -- the form g*x - h for g,h not containing x.
                         -- If g is a nzd mod I, this eliminates x.  Else,
                         -- if g is in the radical of I, add in g to I and return
                         -- else, split with g as: (sat(I,g), (I:sat(I,g)))
  --  Minprimes          -- Mostly for testing(?) Apply minprimes to the annotated ideal
                         -- and keep track of annotated information
  --  IndependentSet     -- Find an independent set (annotate this), find a flattener,
                         -- and split using flattener
  --  Factorization -
  --  CharacteristicSets -

splitFunction = new MutableHashTable
-- each function should like like this:
-- splitFunction#MyStrategy = (I, opts) -> ...
    -- I is an AnnotatedIdeal
    -- opts is from options of splitIdeal
    -- return value is tuple (I1s, I2s), where
    --   I1s is a list of AnnotatedIdeal's, known to be prime
    --   I2s is a list of AnnotatedIdeal's, primality unknown

splitFunction#Linear = (I, opts) -> (
    if I.?Linear then return {I};
    J := I.Ideal;
    linears := for x in gens ring J list (
        k := position(J_*, f -> first degree contract(x,f) == 0);
        if k === null then continue;
        m := makeLinearElement(x, J_k);
        J = replaceVariable(J,m);
        m);
    newJ := if #linears === 0 then (
              I.Linear = true;
              I 
            )
            else
              annotatedIdeal(J, join(I.Linears, linears), I.NonzeroDivisors, I.Inverted);
    {newJ}
    )

splitFunction#Birational = (I, opts) -> (
      if I.?Birational then return {I};
      if I.Ideal == 1 then error "got a bad ideal";
      m := findGoodBirationalPoly I.Ideal;
        -- either null or a list {x, g, f=xg-h}, with f in ideal
      if m === null then (
          I.Birational = true;
          return {I};
          );
      splitt := if member(m#1, I.NonzeroDivisors) then null else splitBy(I.Ideal,m#1);
      if splitt === null then (
          -- in this case, m#1 is a nonzerodivisor
          -- we eliminate m#0
          J := eliminateLinear(I.Ideal, m);
          newI := annotatedIdeal(J, 
                                 append(I.Linears, m), 
                                 unique append(I.NonzeroDivisors, m#1),
                                 I.Inverted);
          -- if we wanted to, we could also place newI onto the "prime" list
          -- if newI.Ideal is generatedby one irreducible element
          return {newI};
          );

      (J1,J2) := splitt;  -- two ideals.  The first has m#1 as a non-zero divisor.
      if J1 == 1 then (
          -- i.e. m#1 is in the radical of I.Ideal
          g := m#1//factors/last//product; -- squarefree part of m#1
          if g == 1 then error "also a bad error";
          newI = annotatedIdeal(I.Ideal + ideal g, I.Linears, I.NonzeroDivisors, I.Inverted);
          return {newI};
          );

      {annotatedIdeal(J1, I.Linears, unique append(I.NonzeroDivisors, m#1), I.Inverted), 
       annotatedIdeal(J2, I.Linears, I.NonzeroDivisors, I.Inverted)}
    )


splitFunction#Factorization = (I,opts) -> (
    if I.?Factorization then return {I};
    J := I.Ideal;
    --- originally taken from facGB0 in PD.m2 -- 12/18/2012
    (f, facs) := findElementThatFactors J_*; -- chooses a generator of I that factors
    if #facs == 0 then ( 
        --<< "no elements found that factor" << endl; << "ideal is " << toString I << endl; 
        I.Factorization = true;
        return {I};
    );
    nonzeros := set I.Inverted;
    prev := set{};
    nonzeroFacs := toList(set facs - nonzeros);
    if #nonzeroFacs == 1 and nonzeroFacs#0 != f then
       return {annotatedIdeal(trim(ideal nonzeroFacs#0 + J),
                              I.Linears,
                              I.NonzeroDivisors,
                              I.Inverted)};
    L := for g in nonzeroFacs list (
          -- colon or sum?
          -- Try and fix UseColon?  May not be fixable...
          {*if opts#"UseColon" then (
          --   -- TODO: Find the components that are missing when using colons!
          --   --       This process will miss any component for which g is in I for all g.
          --   J = I:(f // g);
          *}
          {*
          J = (ideal(g) + I.Ideal);
          J = trim ideal apply(J_*, f -> (
                product toList (set ((factors f)/last) - nonzeros)
              ));
          *}
          J = I + ideal(g);
          J = trim squarefreeGenerators(J,"SquarefreeFactorSize" => opts#"SquarefreeFactorSize");
          J.Inverted = toList (set(J.Inverted) + prev);
          prev = prev + set{g};
          if numgens J.Ideal === 1 and J.Ideal_0 == 1 then continue else J
    );
    L
)

splitFunction#IndependentSet = (I,opts) -> (
    -- what do we need to stash in the answer from independentSets?
    -- does this really belong in the annotated ideal framework?
    -- create two annotated ideals:
    if isPrime I === "YES" then return {I};
    if I.?IndependentSet then return {I};
    J := I.Ideal;
    if J == 1 then error "Internal error: Input should not be unit ideal.";
    R := ring J;
    hf := if isHomogeneous J then poincare J else null;
    indeps := independentSets(J, Limit=>1);
    basevars := support first indeps;
    if opts.Verbosity > 0 then 
        << "  Choosing: " << basevars << endl;
    (S, SF) := makeFiberRings(basevars,R);
    JS := S.cache#"RtoS" J;
    -- if basevars is empty, then return I, but put in the lex ring.
    -- return value not correct form yet
    if #basevars == 0 then (
        I.IndependentSet = ({},S,SF);
        I.LexGBOverBase = (ideal gens gb JS)_*;
        return {I};
    );
    -- otherwise compute over the fraction field.
    if hf =!= null then gb(JS, Hilbert=>hf) else gb JS;
    --gens gb IS;
    (JSF, coeffs) := minimalizeOverFrac(JS, SF);
    if coeffs == {} then (
        I.IndependentSet = (basevars,S,SF);
        I.LexGBOverBase = JSF;
        {I}
    )
    else (
       facs := (factors product coeffs)/last;
       G := product facs;
       if opts.Verbosity > 0 then
           << "  the factors of the flattener: " << netList(facs) << endl;
       G = S.cache#"StoR" G;
       J1 := saturate(J, G);
       J1ann := annotatedIdeal(J1,I.Linears,unique join(I.NonzeroDivisors,facs),I.Inverted);
       J1ann.IndependentSet = (basevars,S,SF);
       J1ann.LexGBOverBase = JSF;
       if J1 == J then
          {J1ann}
       else (
          J2 := trim (J : J1);
          J2ann := annotatedIdeal(J2,I.Linears,I.NonzeroDivisors,I.Inverted);
          {J1ann,J2ann}
       )
    )
)

splitFunction#Minprimes = (I,opts) -> (
   if isPrime I === "YES" then return {I};
   minPrimesList := minprimes I.Ideal; --get options to work here 
   annotatedMPList := minPrimesList / (x -> (
                                  newI := annotatedIdeal(x,
                                              I.Linears,
                                              I.NonzeroDivisors,
                                              I.Inverted);
                                  newI.isPrime = "YES";
                                  newI));
   annotatedMPList
)

isStrategyDone = method()
isStrategyDone (List,Symbol) := (L,strat) ->
  all(L, I -> I#?strat or (I.?isPrime and I.isPrime === "YES"))

splitUntil = method(Options => options splitIdeal)

splitUntil (Ideal,Symbol,ZZ) := 
splitUntil (Ideal,Symbol,InfiniteNumber) := opts -> (I,strat,n) -> 
   splitUntil(annotatedIdeal(I,{},{},{}), strat,n,opts)

splitUntil (AnnotatedIdeal,Symbol,ZZ) := 
splitUntil (AnnotatedIdeal,Symbol,InfiniteNumber) := opts -> (I,strat,n) -> 
   splitUntil({I},strat,n,opts)

splitUntil (List,Symbol,ZZ) := 
splitUntil (List,Symbol,InfiniteNumber) := opts -> (L,strat,n) -> (
   i := 0;
   primeList := {};
   loopList := L;
   while i < n and not isStrategyDone(loopList,strat) do (
      loopList = loopList / (x -> splitFunction#strat(x,opts)) // flatten / flagIsPrime;
      if opts.Verbosity > 0 then (
          knownPrimes := #select(loopList, I -> isPrime I === "YES");
          notknownPrimes := #loopList - knownPrimes;
          << "  Strategy: " << pad(toString strat,18) << " #primes = " << knownPrimes <<
             " #other = " << notknownPrimes << endl;
      );
      i = i + 1;
   );
   loopList
)

splitIdeal Ideal := opts -> I -> splitIdeal({annotatedIdeal(I,{},{},{})}, opts)
splitIdeal AnnotatedIdeal := opts -> I -> splitIdeal({I},opts)
splitIdeal List := opts -> L -> (
    strat := opts.Strategy;
    if not instance (strat,List) then strat = {strat};
    stratPairs := for s in strat list (
       if not instance(s,Sequence) then s = (s,infinity);
       if not member(first s,{Linear,Birational,Factorization,IndependentSet,Minprimes}) then
          error ("Unknown strategy " | toString s | " given.");
       s
    );
    loopList := L;
    for s in stratPairs do (
       loopList = splitUntil(loopList,s#0,s#1);
    );
    loopList
)

------------------------------------------------------------

end

restart
g = (n,opts) -> (n >= 15,n+1)
gComp = composeUntil(g,20)
gComp(0,{})

restart
debug needsPackage "PD"
  R1 = QQ[d, f, j, k, m, r, t, A, D, G, I, K];
  I1 = ideal ( I*K-K^2, r*G-G^2, A*D-D^2, j^2-j*t, d*f-f^2, d*f*j*k - m*r, A*D - G*I*K);
time  minprimesViaBirationalSplit I1;
time minprimes I1;
time decompose I1;
C = time   birationalSplit I1
D =  C/annotatedIdeal
D/isPrime
D/ideal
minprimes D_0
(z1,z2) = equidimSplitOneStep I1
z1
z2
