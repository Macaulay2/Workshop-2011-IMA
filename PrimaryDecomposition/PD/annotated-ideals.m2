-- part of PD.m2, uses code from there too

AnnotatedIdeal = new Type of MutableHashTable
-- fields of this type:
--  A.Ideal
--  A.Linear
--  A.NonzeroDivisors
--  A.BirationalSplitCompleted this exists means: birational split failed to split the ideal
--  A.LinearSplitCompleted: if this field exists, then no linear polys in the ideal

-- An "annotated ideal" is a tuple (I, L, NZ)
-- where I is an ideal (in a subset of the variables)
-- L is a list of (x, g, f), where 
--   x is a variable (not appearing in I at all)
--   g is a poly not involving x
--     g is  monic
--   f = xg-h is in the original ideal (leadTerm f is not nec leadTerm(xg))
-- NZ: list of known nonzero-divisors "need more detail here"
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
        symbol Linear => linears, 
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
     if #linears === 0 then newI.LinearSplitCompleted = true;
     newI
     )

net AnnotatedIdeal := (I) -> (
    net new HashTable from {
        "Ideal" => if numgens I.Ideal === 0 then net I.Ideal else netList (I.Ideal)_*, 
        "Linears" => netList (I.Linear)}
    )

ring AnnotatedIdeal := (I) -> ring I.Ideal

ideal AnnotatedIdeal := (I) -> (
    --F := product I.NonzeroDivisors;
    F := product unique join(I.Linear / (x -> x#1),I.Inverted);
    I1 := ideal(I.Linear/last);
    I2 := I.Ideal;
    I3 := if numgens I1 === 0 then I2 else if numgens I2 === 0 then I1 else I1+I2;
    if F == 1 then I3 else saturate(I3, F)
    )

isPrime AnnotatedIdeal := (I) -> (
    if not I.?isPrime then (I.isPrime = 
        if numgens I.Ideal == 0 then "YES" else "UNKNOWN"
        );
    I.isPrime
    )

nzds = method()
nzds AnnotatedIdeal := (I) -> I.NonzeroDivisors
------------------------------------------------------------
-- splitIdeal code
splitIdeal = method(Options => {Strategy=>null, Verbosity=>1})
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
    if I.?LinearSplitCompleted then return ({},{I});
    J := I.Ideal;
    linears := for x in gens ring J list (
        k := position(J_*, f -> first degree contract(x,f) == 0);
        if k === null then continue;
        m := makeLinearElement(x, J_k);
        J = replaceVariable(J,m);
        m);
    newJ := if #linears === 0 then (
              I.LinearSplitCompleted = true;
              I 
              )
            else
              annotatedIdeal(J, join(I.Linear, linears), I.NonzeroDivisors, I.Inverted);
    ({}, {newJ})
    )

splitFunction#Birational = (I, opts) -> (
      if I.?BirationalSplitCompleted then return ({},{I});
      if I.Ideal == 1 then error "got a bad ideal";
      m := findGoodBirationalPoly I.Ideal;
        -- either null or a list {x, g, f=xg-h}, with f in ideal
      if m === null then (
          I.BirationalSplitCompleted = true;
          return if isPrime I === "YES" then ({I},{}) else ({},{I});
          );
      splitt := if member(m#1, I.NonzeroDivisors) then null else splitBy(I.Ideal,m#1);
      if splitt === null then (
          -- in this case, m#1 is a nonzerodivisor
          -- we eliminate m#0
          J := eliminateLinear(I.Ideal, m);
          newI := annotatedIdeal(J, 
                                 append(I.Linear, m), 
                                 unique append(I.NonzeroDivisors, m#1),
                                 I.Inverted);
          -- if we wanted to, we could also place newI onto the "prime" list
          -- if newI.Ideal is generatedby one irreducible element
          return if isPrime newI === "YES" then ({newI},{}) else ({},{newI});
          );

      (J1,J2) := splitt;  -- two ideals.  The first has m#1 as a non-zero divisor.
      if J1 == 1 then (
          -- i.e. m#1 is in the radical of I.Ideal
          g := m#1//factors/last//product; -- squarefree part of m#1
          if g == 1 then error "also a bad error";
          newI = annotatedIdeal(I.Ideal + ideal g, I.Linear, I.NonzeroDivisors, I.Inverted);
          return if isPrime newI === "YES" then ({newI},{}) else ({},{newI});
          );

      ({},
       {annotatedIdeal(J1, I.Linear, unique append(I.NonzeroDivisors, m#1), I.Inverted), 
           annotatedIdeal(J2, I.Linear, I.NonzeroDivisors, I.Inverted)}
       )
    )

splitFunction#Factorization = (I,opts) -> (
    if I.?FactorizationSplitCompleted then return ({},{I});
    J := I.Ideal;
    --- originally taken from facGB0 in PD.m2 -- 12/18/2012
    (f, facs) := findElementThatFactors J_*; -- chooses a generator of I that factors
    if #facs == 0 then ( 
        --<< "no elements found that factor" << endl; << "ideal is " << toString I << endl; 
        I.FactorizationSplitCompleted = true;
        if #(J_*) == 1 then (
            I.isPrime = "YES";
            return ({I},{})
        )
        else
           return ({},{I});
        );
    nonzeros := set I.Inverted;
    prev := set{};
    nonzeroFacs := toList(set facs - nonzeros);
    if #nonzeroFacs == 1 and nonzeroFacs#0 != f then
       return ({},{annotatedIdeal(trim(ideal nonzeroFacs#0 + J),
                                  I.Linear,
                                  I.NonzeroDivisors,
                                  I.Inverted)});
    L := for g in nonzeroFacs list (
          -- colon or sum?
          -- Try and fix UseColon?  May not be fixable...
          {*if opts#"UseColon" then (
          --   -- TODO: Find the components that are missing when using colons!
          --   --       This process will miss any component for which g is in I for all g.
          --   J = I:(f // g);
          *}
          J = (ideal(g) + I.Ideal);
          J = trim ideal apply(J_*, f -> (
                product toList (set ((factors f)/last) - nonzeros)
              ));
          result := annotatedIdeal(J, I.Linear, I.NonzeroDivisors, toList (nonzeros + prev));
          prev = prev + set{g};
          if numgens J === 1 and J_0 == 1 then continue else result
    );
    ({}, L)
)

splitFunction#Minprimes = (I,opts) -> (
   if isPrime I === "YES" then return ({I},{});
   minPrimesList := minprimes I.Ideal; --get options to work here 
   annotatedMPList := minPrimesList / (x -> (
                                  newI := annotatedIdeal(x,
                                              I.Linear,
                                              I.NonzeroDivisors,
                                              I.Inverted);
                                  newI.isPrime = "YES";
                                  newI));
   (annotatedMPList,{})              
)

splitIdeal Ideal := (opts) -> (I) -> splitIdeal(annotatedIdeal(I,{},{},{}), opts)
splitIdeal AnnotatedIdeal := (opts) -> (I) -> splitIdeal({},{I},opts)
--splitIdeal(List,List) := opts -> (L1,L2) -> (
--    newL2 := L2/(x -> splitIdeal(x,opts));
--    knownPrimes := join(L1, flatten(newL2/first));
--    notknownPrimes := flatten(newL2/last);
--    (knownPrimes, notknownPrimes)
--    )
splitIdeal(List,List) := opts -> (L1,L2) -> (
    strat := opts.Strategy;
    if not instance (strat,List) then strat = {strat};
    while #strat > 0 and #L2 > 0 do (
       if opts.Verbosity > 0 then
          << "Splitting using strategy " << first strat << endl;
       newL2 := L2/(x -> splitFunction#(first strat)(x,opts));
       strat = drop(strat,1);
       knownPrimes := join(L1, flatten(newL2/first));
       notknownPrimes := flatten(newL2/last);
       if opts.Verbosity > 0 then (
          << "  Known as primes : " << #knownPrimes << endl;
          << "  Not known as primes : " << #notknownPrimes << endl;
       );
       (L1,L2) = (knownPrimes, notknownPrimes);
    );
    (L1,L2)
)
splitIdeal List := opts -> (L) -> splitIdeal({},L,opts)

------------------------------------------------------------

end

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
