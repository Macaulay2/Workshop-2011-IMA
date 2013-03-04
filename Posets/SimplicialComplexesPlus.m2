-- Copyright 2011, 2012, 2013: David Cook II and Gwyn Whieldon
-- You may redistribute this file under the terms of the GNU General Public
-- License as published by the Free Software Foundation, either version 2
-- of the License, or any later version.

------------------------------------------
------------------------------------------
-- Header 
------------------------------------------
------------------------------------------

if version#"VERSION" <= "1.4" then (
    needsPackage "SimplicialComplexes";
    needsPackage "Graphs";
    )

newPackage select((
    "SimplicialComplexesPlus",
    Version => "0.3",
    Date => "27. February 2013",
    Authors => {
            {Name => "Gwyn Whieldon", Email => "whieldon@hood.edu", HomePage => "http://www.hood.edu/Academics/Departments/Mathematics/Faculty/Gwyneth-Whieldon.html"},
            {Name => "David Cook II", Email => "dcook8@nd.edu", HomePage => "http://www.nd.edu/~dcook8/"}
    },
    Headline => "Additional operations on simplicial complexes",
    Configuration => { },
    DebuggingMode => true,
    if version#"VERSION" > "1.4" then PackageExports => {"SimplicialComplexes", "Graphs"}
    ), x -> x =!= null)

if version#"VERSION" <= "1.4" then (
    needsPackage "SimplicialComplexes";
    needsPackage "Graphs";
    )

export {
    --
    -- Enumerators & constructors
    "cliqueComplex",
    "coverComplex",
    "crossPolytopeBoundary",
    "independenceComplex",
    "nerveComplex",
        "IsMultigraded",
    "randomSimplicialComplex",
    "randomSquarefreeIdeal",
    "revlexComplex",
    "simplex",
    "simplexBoundary",
    --
    -- Operations
    "barycentricSubdivision",
    "bsdFacetLabels",
        "BSDVarMap",
    "combinatorialJoin",
    "combinatorialShift",
    "disjointUnion",
    "faceDelete",
    "inducedSubcomplex",
    "polarise",
    "simplicialCone",
    "skeleton",
    "star",
    "suspension",
    "underlyingGraph",
    --
    -- Properties & invariants
    "connectedComponents",
    "eulerCharacteristic",
    "gVector",
    "hVector",
    "isConnected",
    "isFlag",
    --
    -- GAP
    "gapSC",
    "gapSCBetti",
    "gapSCHomology",
    "gapSCLibrary",
    "gapSCLibrarySize"
    }

------------------------------------------
------------------------------------------
-- Methods
------------------------------------------
------------------------------------------

------------------------------------------
-- Enumerators & constructors
------------------------------------------

cliqueComplex = method(Options => {symbol CoefficientRing => QQ})
cliqueComplex Graph := SimplicialComplex => opts -> G -> (
    V := vertices G;
    n := #V;
    x := local x;
    R := (opts.CoefficientRing)(monoid [x_0..x_(n-1)]);
    vtoi := hashTable apply(n, i -> V_i => i);
    nonEdges := subsets(n, 2) - set (toList \ edges G);
    simplicialComplex monomialIdeal apply(nonEdges, e -> R_(vtoi#(first e)) * R_(vtoi#(last e)))
    )

coverComplex = method(Options => {symbol CoefficientRing => QQ})
coverComplex Graph := SimplicialComplex => opts -> G -> simplicialComplex (ideal dual independenceComplex(G, opts))_*

crossPolytopeBoundary = method(Options => {symbol CoefficientRing => QQ})
crossPolytopeBoundary ZZ := SimplicialComplex => opts -> n -> (
    x := local x;
    y := local y;
    R := (opts.CoefficientRing)(monoid [x_1..x_n,y_1..y_n]);
    simplicialComplex monomialIdeal apply(toList(0..<n), i -> R_i * R_(n+i))
    )

independenceComplex = method(Options => {symbol CoefficientRing => QQ})
independenceComplex Graph := SimplicialComplex => opts -> G -> (
    V := vertices G;
    n := #V;
    x := local x;
    R := (opts.CoefficientRing)(monoid [x_0..x_(n-1)]);
    vtoi := hashTable apply(n, i -> V_i => i);
    simplicialComplex monomialIdeal apply(toList \ edges G, e -> R_(vtoi#(first e)) * R_(vtoi#(last e)))
    )

nerveComplex = method(Options => {symbol CoefficientRing => QQ, symbol IsMultigraded => false})
nerveComplex Graph := SimplicialComplex => opts -> G -> (
    m := #edges G;
    e := local e;
    R := (opts.CoefficientRing)(
        if opts.IsMultigraded then monoid[e_1..e_m, Degrees => entries map(ZZ^m, ZZ^m, 1)]
        else monoid[e_1..e_m]);
    I := apply(vertices G, v -> select(0..m-1, i -> member(v, (edges G)#i)));
    simplicialComplex apply(I, L -> product(L, i -> R_i))
    )
nerveComplex SimplicialComplex := SimplicialComplex => opts -> D -> (
    F := flatten entries facets D;
    m := #F;
    f := local f;
    R := (opts.CoefficientRing)(
        if opts.IsMultigraded then monoid[f_1..f_m, Degrees => entries map(ZZ^m, ZZ^m, 1)]
        else monoid[f_1..f_m]);
    I := apply(gens ring D, v -> select(0..m-1, i -> member(v, support F_i)));
    simplicialComplex apply(I, L -> product(L, i -> R_i))
    )

--TODO
--Effect probability of a face?
randomSimplicialComplex = method(Options => {symbol CoefficientRing => QQ})
randomSimplicialComplex (ZZ, ZZ, ZZ) := SimplicialComplex => opts -> (n, d, f) -> ()
randomSimplicialComplex (ZZ, ZZ) := SimplicialComplex => opts -> (n, d) -> ()
randomSimplicialComplex ZZ := SimplicialComplex => opts -> n -> ()

--TODO
--Effect probability of a generator?
randomSquarefreeIdeal = method()
randomSquarefreeIdeal Ring := MonomialIdeal => R -> ()
randomSquarefreeIdeal (Ring, ZZ) := MonomialIdeal => (R, d) -> ()
randomSquarefreeIdeal (Ring, ZZ, ZZ) := MonomialIdeal => (R, d, g) -> ()

revlexComplex = method()
revlexComplex SimplicialComplex := SimplicialComplex => D -> (
    R := (coefficientRing ring D)(monoid[gens ring D]);
    f := fVector D;
    simplicialComplex flatten apply(dim D + 1, i -> take(rsort (product \ subsets(gens R, i+1)), f#i))
    )

simplex = method(Options => {symbol CoefficientRing => QQ})
simplex ZZ := SimplicialComplex => opts -> (n, K) -> simplexBoundary(n, n+1, opts)

simplexBoundary = method(Options => {symbol CoefficientRing => QQ})
simplexBoundary (ZZ, ZZ) := SimplicialComplexes => opts -> (n, k) -> (
    x := local x;
    R := (opts.CoefficientRing)(monoid [x_0..x_n]);
    simplicialComplex(product \ subsets(gens R, k))
    )
simplexBoundary ZZ := SimplicialComplex => opts -> n -> simplexBoundary(n, n, opts)


------------------------------------------
-- Operations
------------------------------------------

barycentricSubdivision = method()
barycentricSubdivision SimplicialComplex := SimplicialComplex => D -> (
    S := apply(flatten apply(1 + dim D, d -> first entries faces(d, D)), indices);
    x := local x;
    R := (coefficientRing ring D)(monoid [apply(S, i -> x_i)]);
    idx := hashTable apply(#S, i -> S_i => R_i);
    -- Build the complex by looking at the non-faces
    bsdD := simplicialComplex monomialIdeal for P in subsets(S, 2) list if not isSubset(P_0, P_1) and not isSubset(P_1, P_0) then idx#(P_0)*idx#(P_1) else continue;
    bsdD.cache.BSDVarMap = hashTable apply(S, s -> idx#s => product(s, j -> (ring D)_j));
    bsdD
    )

bsdFacetLabels = method()
bsdFacetLabels SimplicialComplex := List => D -> (
    if not D.cache.?BSDVarMap then error "The simplicial complex was not generated by barycentricSubdivision.";
    apply(first entries facets D, F -> apply(support F, v -> D.cache.BSDVarMap#v))
    )

combinatorialJoin = method()
combinatorialJoin (SimplicialComplex, SimplicialComplex) := SimplicialComplex => (A, B) -> (
    R := (coefficientRing ring A)(monoid [gens ring A, gens ring B]);
    FA := apply(flatten entries facets A, F -> sub(F, R));
    FB := apply(flatten entries facets B, F -> sub(F, R));
    simplicialComplex flatten apply(FA, a -> apply(FB, b -> a*b))
    )

--TODO
combinatorialShift = method()
combinatorialShift SimplicialComplex := SimplicialComplex => D -> ()

disjointUnion = method()
disjointUnion (SimplicialComplex, SimplicialComplex) := SimplicialComplex => (A, B) -> (
    nA := #gens ring A;
    nB := #gens ring B;
    a := local a;
    b := local b;
    R := (coefficientRing ring A)(monoid [a_1..a_nA, b_1..b_nB]);
    FA := apply(flatten entries facets A, F -> product(indices F, i -> R_i));
    FB := apply(flatten entries facets B, F -> product(indices F, i -> R_(i + nA)));
    simplicialComplex join(FA, FB)
    )

faceDelete = method()
faceDelete (RingElement, SimplicialComplex) := SimplicialComplex => (s, D) -> simplicialComplex (monomialIdeal s + monomialIdeal D)

inducedSubcomplex = method()
inducedSubcomplex (SimplicialComplex, List) := SimplicialComplex => (D, W) -> (
    if not isSubset(W, gens ring D) then error "The subset W must be a subset of the vertices of D.";
    S := (coefficientRing ring D)(monoid [W]);
    antiW := set gens ring D - set W;
    simplicialComplex apply(first entries facets D, f -> sub(product(support f - antiW), S))
    )

polarise = method()
polarise Ideal := SimplicialComplex => I -> (
    if not isMonomialIdeal I then I = monomialIdeal I;
    n := #gens ring I;
    E := flatten (exponents \ I_*);
    A := max \ transpose E;
    offset := accumulate(plus, join({0,0},A));
    x := local x;
    R := (coefficientRing ring I)(monoid [flatten apply(n, j -> apply(A_j, k -> x_{j, k}))]);
    monomialIdeal apply(#E, i -> product(n, j -> product(E_i_j, k -> R_(offset_j + k))))
    )

simplicialCone = method(Options => {symbol Variable => "X"})
simplicialCone SimplicialComplex := SimplicialComplex => opts -> D -> combinatorialJoin(D, simplicialComplex gens (coefficientRing ring D)(monoid [opts.Variable]))

skeleton = method()
skeleton (SimplicialComplex, ZZ) := SimplicialComplex => (D, k) -> simplicialComplex flatten apply(k + 1, i -> first entries faces(i, D))

star = method()
star (RingElement, SimplicialComplex) := List => (s, D) -> (
    sss := set support s;
    select(flatten apply(1 + dim D, i -> first entries faces(i, D)), f -> #(set support f * sss) != 0)
    )

suspension = method(Options => {symbol Variable => {"X", "Y"}})
suspension SimplicialComplex := SimplicialComplex => opts -> D -> combinatorialJoin(D, simplicialComplex gens (coefficientRing ring D)(monoid [opts.Variable_0, opts.Variable_1]))

underlyingGraph = method()
underlyingGraph SimplicialComplex := Graph => D -> (
    E := support \ first entries faces(1, D);
    S := gens ring D - set flatten E;
    graph(E, Singletons => S)
    )

------------------------------------------
-- Properties & invariants
------------------------------------------

connectedComponents = method()
connectedComponents SimplicialComplex := List => D -> (
    G := underlyingGraph D;
    V := vertices G;
    while #V > 0 list (
        R := reachable(G, {first V});
        V = V - set R;
        R
        )
    )

eulerCharacteristic = method()
eulerCharacteristic SimplicialComplex := ZZ => D -> (
    f := fVector D;
    sum(dim D + 1, i -> (-1)^i * f#i)
    )

gVector = method()
gVector SimplicialComplex := HashTable => D -> (
    h := hVector D;
    d := dim D + 1;
    hashTable prepend(0 => 1, apply(toList(1..(d+1)//2), j -> j => h#j - h#(j-1)))
    )

hVector = method()
hVector SimplicialComplex := HashTable => D -> (
    f := fVector D;
    d := dim D + 1;
    hashTable apply(toList(0..d), j -> j => sum(j+1, i -> (-1)^(j-i)*binomial(d - i, j - i) * f#(i-1)))
    )

isConnected = method()
isConnected SimplicialComplex := Boolean => D -> (
    G := underlyingGraph D;
    #reachable(G, {first vertices G}) == #vertices G
    )

isFlag = method()
isFlag SimplicialComplex := Boolean => D -> all((monomialIdeal D)_*, g -> first degree g <= 2)

------------------------------------------
-- GAP
------------------------------------------

gapSC = method()
gapSC (SimplicialComplex, String) := String => (D, S) -> concatenate(S, ":=SCFromFacets(", toString apply(new Array from flatten entries facets D, f -> new Array from indices f), ");")
gapSC SimplicialComplex := String => D -> gapSC(D, "Delta")

--TODO
gapSCBetti = method()
gapSCBetti (SimplicialComplex, ZZ) := List => (D, p) -> ()

--TODO
gapSCHomology = method()
gapSCHomology SimplicialComplex := List => D -> ()

--TODO
gapSCLibrary = method(Options => {symbol CoefficientRing => QQ})
gapSCLibrary String := SimplicialComplex => opts -> D -> ()
gapSCLibrary ZZ := SimplicialComplex => opts -> D -> ()

--TODO
gapSCLibrarySize = method()
installMethod(gapSCLibrarySize, () -> 1)

------------------------------------------
------------------------------------------
-- Documentation
------------------------------------------
------------------------------------------

beginDocumentation()

-- Front Page
doc ///
    Key
        SimplicialComplexesPlus
    Headline
        a package for additional operations on simplicial complexes
    Description
        Text

            This package adds a number of features to the @TO "SimplicialComplexes"@ package, 
            including barycentric subdivision, simplex and boundary of simplicial constructions,
            combinatorial join, construction of the cross polytope, and exportation of 
            Macaulay2 code for a simplicial complex into GAP format.
///

