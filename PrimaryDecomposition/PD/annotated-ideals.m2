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

annotatedIdeal = method()
annotatedIdeal(Ideal, List, List) := (I, linears, nzds) -> (
    -- I is an ideal
    -- linears is a list of LinearElement's (x, g, f), where 
    --   f = xg-h is in the ideal, 
    --   g and h don't involve x
    --   and g is monic over the base field
    -- nzds is a list of polynomials which are nzds's of the associated ideal
    -- The associated ideal is:
    --   saturate(I + ideal(linears/last), product nzds)
    nzds1 := nzds/factors//flatten;
    nzds2 := select(nzds1, g -> #g > 0);
    nzds3 := nzds2 / last // unique;
    new AnnotatedIdeal from {
        symbol Ideal => I, 
        symbol Linear => linears, 
        symbol NonzeroDivisors => nzds3
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
     newI := annotatedIdeal(I, linears, {});
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
    F := product I.NonzeroDivisors;
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
splitIdeal = method(Options => {Strategy=>null})
  -- possible Strategy values:
  --  Linear, Birational, IndependentSet, Factorization, CharacteristicSets

splitFunction = new MutableHashTable
-- each function should like like this:
-- splitFunction#MyStrategy = (I, opts) -> ...
    -- I is an AnnotatedIdeal
    -- opts is from options of splitIdeal
    -- return value is triple (wasSimplified, I1s, I2s), where
    --   wasSimplified: Boolean,
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
              annotatedIdeal(J, join(I.Linear, linears), I.NonzeroDivisors);
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
                                 unique append(I.NonzeroDivisors, m#1));
          -- if we wanted to, we could also place newI onto the "prime" list
          -- if newI.Ideal is generatedby one irreducible element
          return if isPrime newI === "YES" then ({newI},{}) else ({},{newI});
          );

      (J1,J2) := splitt;  -- two ideals.  The first has m#1 as a non-zero divisor.
      if J1 == 1 then (
          -- i.e. m#1 is in the radical of I.Ideal
          g := m#1//factors/last//product; -- squarefree part of m#1
          if g == 1 then error "also a bad error";
          newI = annotatedIdeal(I.Ideal + ideal g, I.Linear, I.NonzeroDivisors);
          return if isPrime newI === "YES" then ({newI},{}) else ({},{newI});
          );

      ({},
       {annotatedIdeal(J1, I.Linear, unique append(I.NonzeroDivisors, m#1)), 
           annotatedIdeal(J2, I.Linear, I.NonzeroDivisors)}
       )
    )

splitIdeal Ideal := (opts) -> (I) -> splitIdeal(annotatedIdeal(I,{},{}), opts)
splitIdeal AnnotatedIdeal := (opts) -> (I) -> splitFunction#(opts.Strategy)(I,opts)
splitIdeal(List,List) := opts -> (L1,L2) -> (
    newL2 := L2/(x -> splitIdeal(x,opts));
    knownPrimes := join(L1, flatten(newL2/first));
    notknownPrimes := flatten(newL2/last);
    (knownPrimes, notknownPrimes)
    )
splitIdeal List := opts -> (L) -> splitIdeal({},L,opts)

------------------------------------------------------------

minprimesViaBirationalSplit = method()
minprimesViaBirationalSplit Ideal := (I) -> (
    time C := birationalSplit I;
    D := C/annotatedIdeal;
    E := D/minprimes//flatten;
    F := E/ideal;
    G := F//selectMinimalIdeals;
    G
    )

minprimes AnnotatedIdeal := opts -> (I) -> (
    C := minprimes I.Ideal;
    C / (x -> (
            xa := annotatedIdeal x;
            annotatedIdeal(xa.Ideal, join(I.Linear, xa.Linear), I.NonzeroDivisors)))
    )
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
