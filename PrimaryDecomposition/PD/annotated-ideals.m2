-- part of PD.m2, uses code from there too

AnnotatedIdeal = new Type of MutableHashTable

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
    new AnnotatedIdeal from {symbol Ideal => I, symbol Linear => linears, symbol NonzeroDivisors => nzds3}
    )

annotatedIdeal Ideal := (I) -> (
     -- input: ideal I in a polynomial ring R
     linears := for x in gens ring I list (
         k := position(I_*, f -> first degree contract(x,f) == 0);
         if k === null then continue;
         m := makeLinearElement(x, I_k);
         I = replaceVariable(I,m);
         m);
     annotatedIdeal(I, linears, {})
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
