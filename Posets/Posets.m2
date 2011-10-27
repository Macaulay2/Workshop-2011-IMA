------------------------------------------
-- Currently working on:
------------------------------------------
-- David: Precomputation
-- Gwyn:  Tests (tests not running right now, will be fixed tomorrow)

------------------------------------------
-- To do list:
------------------------------------------
-- New Methods:
    -- Identify comparability graphs
    -- Poset of a resolution

-- Precomputation:
    -- Continue linearly through the file at adjoinMax (line 450) which
    -- has some precomputation finished, but needs more.
    -- **Please double check that I'm not doing anything wonky!**

-- Documentation:
    -- Add a few extended examples
    -- Grammar/spelling check extant nodes

-- Tests
    -- Everything!

-- Several enumerator methods could be made more efficient (avoid "subsets"):
    -- intersectionLattice, hibiIdeal, hibiRing, pPartitionRing 
    
-- Everything above the line below should be removed before the package is submitted.
------------------------------------------

-- Copyright 2011: David Cook II, Sonja Mapes, Gwyn Whieldon
-- You may redistribute this file under the terms of the GNU General Public
-- License Version 2 as published by the Free Software Foundation.

------------------------------------------
------------------------------------------
-- Header 
------------------------------------------
------------------------------------------

if version#"VERSION" <= "1.4" then (
    needsPackage "SimplicialComplexes";
    needsPackage "Graphs";
    needsPackage "FourTiTwo";
    )

newPackage select((
    "Posets",
        Version => "1.0.4", 
        Date => "13. October 2011",
        Authors => {
            {Name => "David Cook II", Email => "dcook@ms.uky.edu", HomePage => "http://www.ms.uky.edu/~dcook/"},
            {Name => "Sonja Mapes", Email => "smapes@math.duke.edu", HomePage => "http://www.math.duke.edu/~smapes/"},
            {Name => "Gwyn Whieldon", Email => "whieldon@hood.edu", HomePage => "http://www.hood.edu/Academics/Departments/Mathematics/Faculty/Gwyneth-Whieldon.html"}
        },
        Headline => "Package for processing posets and order complexes",
        Configuration => {"DefaultPDFViewer" => "open", "DefaultSuppressLabels" => true},
        DebuggingMode => true,
        if version#"VERSION" > "1.4" then PackageExports => {"SimplicialComplexes", "Graphs", "FourTiTwo"}
        ), x -> x =!= null)

if version#"VERSION" <= "1.4" then (
    needsPackage "SimplicialComplexes";
    needsPackage "Graphs";
    needsPackage "FourTiTwo";
    )

-- Load configurations
posets'PDFViewer = if instance((options Posets).Configuration#"DefaultPDFViewer", String) then (options Posets).Configuration#"DefaultPDFViewer" else "open";
posets'SuppressLabels = if instance((options Posets).Configuration#"DefaultSuppressLabels", Boolean) then (options Posets).Configuration#"DefaultSuppressLabels" else true;

export {
    --
    -- Data type & constructor
    "Poset",
        "GroundSet",
        "RelationMatrix",
        "Relations",
    "poset",
    "transitiveClosure",
    --
    -- Derivative non-poset structures
    "comparabilityGraph",
    "hasseDiagram",
    "hibiIdeal",
    "hibiRing",
    "incomparabilityGraph",
    "orderComplex",
        "VariableName",
    "pPartitionRing",
    --
    -- Derivative posets
    "closedInterval",
    "dilworthLattice",
    "distributiveLattice",
        "OriginalPoset",
  --"dual",
    "filter",
    "flagPoset",
    "indexLabeling",
    "labelPoset",
    "naturalLabeling",
    "openInterval",
    "orderIdeal",
    "principalFilter",
    "principalOrderIdeal",
    "subposet",
    --
    -- Operations
    "adjoinMax",
    "adjoinMin",
    "areIsomorphic",
    "augmentPoset",
    "diamondProduct",
    "dropElements",
    "isomorphism",
  --"product",
    "removeIsomorphicPosets",
    "union",
    --
    -- Enumerators
    "booleanLattice",
    "chain",
    "divisorPoset",
    "dominanceLattice",
    "facePoset",
    "intersectionLattice",
    "lcmLattice",
    "partitionLattice",
        "setPartition",
    "projectivizeArrangement",
    "randomPoset",
        "Bias",
    "standardMonomialPoset",
    "youngSubposet",
    --
    -- TeX & GAP
    "displayPoset",
    "gapPosetConversion",
    "outputTexPoset",
    "texPoset",
        "Jitter",
        "PDFViewer",
        "SuppressLabels",
    --
    -- Vertices & vertex properties
    "atoms",
    "compare",
    "connectedComponents",
    "filtration",
    "joinExists",
    "joinIrreducibles",
    "maximalElements",
    "meetExists",
    "meetIrreducibles",
    "minimalElements",
    "posetJoin",
    "posetMeet",
    "rankFunction",
    "rankPoset",
    --
    -- Relations & relation properties
    "allRelations",
    "antichains",
    "chains",
    "coveringRelations",
    "flagChains",
    "isAntichain",
    "linearExtensions",
    "maximalAntichains",
    "maximalChains",
    --
    -- Enumerative invariants
    "characteristicPolynomial",
    "flagfPolynomial",
    "flaghPolynomial",
    "fPolynomial",
    "greeneKleitmanPartition",
    "hPolynomial",
    "moebiusFunction",
    "rankGeneratingFunction",
    "zetaPolynomial",
    --
    -- Properties
    "dilworthNumber",
  --"height", -- exported by Core
    "isAtomic",
    "isBounded",
    "isConnected",
    "isDistributive",
    "isEulerian",
    "isGeometric",
    "isGraded",
    "isLattice",
    "isLowerSemilattice",
    "isLowerSemimodular",
    "isModular",
    "isRanked",
    "isSperner",
    "isStrictSperner",
    "isUpperSemilattice",
    "isUpperSemimodular"
    }

------------------------------------------
------------------------------------------
-- Methods
------------------------------------------
------------------------------------------

------------------------------------------
-- Non-exported, strongly prevalent functions
------------------------------------------

indexElement := (P,A) -> position(P.GroundSet, i -> i === A);

principalOrderIdeal' := (P, i) -> positions(flatten entries(P.RelationMatrix_i), j -> j != 0)

principalFilter' := (P, i) -> positions(first entries(P.RelationMatrix^{i}), j -> j != 0)

------------------------------------------
-- Data type & constructor
------------------------------------------

Poset = new Type of HashTable

poset = method()
poset(List, List, Matrix) := Poset => (G, R, M) -> (
    if rank M =!= #G then error "The relations failed anti-symmetry.";
    new Poset from {
        symbol GroundSet => G,
        symbol Relations => toList \ R,
        symbol RelationMatrix => M,
        symbol cache => new CacheTable
        })
poset (List, List) := Poset => (G, R) -> poset(G, R = toList \ R, transitiveClosure(G, R))
poset (List, Function) := Poset => (G, cmp) -> (
    try (
        M := matrix for a in G list for b in G list if cmp(a,b) then 1 else 0;
        R := flatten for i to #G-1 list for j to #G-1 list if i != j and M_j_i == 1 then {G_i, G_j} else continue;
    ) else error "The comparison function cmp must (i) take two inputs, (ii) return a Boolean, and (iii) be defined for all pairs of G.";
    poset(G, R, M)
    )
poset List := Poset => R -> poset(unique flatten (R = toList \ R), R);

Poset _ ZZ := Thing => (P, i) -> P.GroundSet#i
Poset _ List := List => (P, L) -> P.GroundSet_L
installMethod(symbol _*, Poset, P -> P.GroundSet)

toString Poset := 
toExternalString Poset := String => P -> "poset(" | toExternalString P.GroundSet | ", " | toExternalString P.Relations | ", " | toString P.RelationMatrix | ")"

-- Returns a matrix M such that M_(i,j) = 1 if G_i <= G_j, and 0 otherwise
transitiveClosure = method()
transitiveClosure (List, List) := Matrix => (G, R) -> (
    idx := hashTable apply(#G, i -> G_i => i);
    R = apply(R, r -> {idx#(first r), idx#(last r)});
    H := floydWarshall digraph hashTable apply(#G, i -> i => set apply(select(R, r -> first r == i), r -> last r));
    matrix apply(#G, i -> apply(#G, j -> if H#(i, j) < 1/0. then 1 else 0))
    )

------------------------------------------
-- Derivative non-poset structures
------------------------------------------

-- NB: Renames vertices, otherwise it produces the wrong graph in some cases.
comparabilityGraph = method()
comparabilityGraph Poset := Graph => P -> (
    E := flatten for i from 0 to #P.GroundSet - 1 list for j from i+1 to #P.GroundSet - 1 list
        if P.RelationMatrix_i_j == 1 or P.RelationMatrix_j_i == 1 then {i, j} else continue;
    fE := unique flatten E;
    graph(E, Singletons => select(#P.GroundSet, i -> not member(i, fE)))
    )

-- NB: Renames vertices, otherwise it produces the wrong graph in some cases.
hasseDiagram = method()
hasseDiagram Poset := Digraph => P -> (
    if not P.cache.?coveringRelations then coveringRelations P;
    digraph merge(applyValues(partition(first, P.cache.coveringRelations), v -> last \ v), hashTable apply(#P.GroundSet, i -> i => {}), join)
    )

-- NB: Renames vertices, otherwise it produces the wrong ideal in some cases.
hibiIdeal = method(Options => { symbol CoefficientRing => QQ })
hibiIdeal (Poset) := MonomialIdeal => opts -> (P) -> (
    G := set toList(0 ..< #P.GroundSet);
    O := unique apply(#P.GroundSet, i -> principalOrderIdeal'(P, i));
    J := unique apply(subsets(#O), s -> sort unique flatten O_s);
    x := local x;
    y := local y;
    R := (opts.CoefficientRing)(monoid [x_0..x_(#P.GroundSet-1),y_0..y_(#P.GroundSet-1)]);
    monomialIdeal apply(J, I -> product(I, i -> R_i) * product(toList(G - I), j -> R_(#P.GroundSet + j)))
    )

-- NB: Renames vertices, otherwise it produces the wrong ideal in some cases.
hibiRing = method(Options => { symbol CoefficientRing => QQ, symbol Strategy => "kernel" })
hibiRing (Poset) := QuotientRing => opts -> (P) -> (
    if opts.Strategy =!= "kernel" and opts.Strategy =!= "4ti2" then error "The option Strategy must either be 'kernel' or '4ti2'.";
    t := local t; x := local x; y := local y;
    R := (opts.CoefficientRing)(monoid [x_0..x_(#P.GroundSet-1),y_0..y_(#P.GroundSet-1)]);
    O := unique apply(#P.GroundSet, i -> principalOrderIdeal'(P, i));
    J := unique apply(subsets(#O), s -> sort unique flatten O_s);
    S := (opts.CoefficientRing)(monoid[apply(J, I -> t_I)]);
    G := set toList(0 ..< #P.GroundSet);
    M := apply(J, I -> product(I, i -> R_i) * product(toList(G - I), j -> R_(#P.GroundSet + j)));
    if opts.Strategy === "kernel" then S/kernel map(R, S, matrix {M})
    else if opts.Strategy === "4ti2" then (
        N := matrix transpose apply(indices \ M, I -> apply(numgens R, j -> if member(j, I) then 1 else 0));
        S/toricGroebner(N, S)
        )
    )

-- NB: Renames vertices, otherwise it produces the wrong graph in some cases.
incomparabilityGraph = method()
incomparabilityGraph Poset := Graph => P -> (
    E := flatten for i from 0 to #P.GroundSet - 1 list for j from i+1 to #P.GroundSet - 1 list
        if P.RelationMatrix_i_j == 0 and P.RelationMatrix_j_i == 0 then {i, j} else continue;
    S := toList(0 ..< #P.GroundSet) - set unique flatten E;
    graph(E, Singletons => S)
    )

-- NB: Renames vertices, otherwise it produces the wrong simplicial complex in some cases.
orderComplex = method(Options => { symbol VariableName => getSymbol "v", symbol CoefficientRing => QQ })
orderComplex (Poset) := SimplicialComplex => opts -> (P) -> (
    E := flatten for i from 0 to #P.GroundSet - 1 list for j from i+1 to #P.GroundSet - 1 list
        if P.RelationMatrix_i_j == 0 and P.RelationMatrix_j_i == 0 then {i, j} else continue;
    s := opts.VariableName;
    R := (opts.CoefficientRing)(monoid [s_0..s_(#P.GroundSet - 1)]);
    simplicialComplex if #E > 0 then monomialIdeal apply(E, e -> R_(e_0) * R_(e_1)) else {product gens R}
    )

pPartitionRing = method(Options => { symbol CoefficientRing => QQ, symbol Strategy => "kernel" })
pPartitionRing (Poset) := QuotientRing => opts -> (P) -> (
    if opts.Strategy =!= "kernel" and opts.Strategy =!= "4ti2" then error "The option Strategy must either be 'kernel' or '4ti2'.";
    O := unique apply(#P.GroundSet, i -> principalOrderIdeal'(P, i));
    J := select(unique apply(subsets(#O), s -> sort unique flatten O_s), I -> isConnected subposet(P, P.GroundSet_I));
    t := local t;
    S := (opts.CoefficientRing)(monoid [apply(J, I -> t_I)]);
    if opts.Strategy === "kernel" then (
        R := (opts.CoefficientRing)(monoid [t_0..t_(#P.GroundSet-1)]);   
        M := matrix{apply(J, I -> product(I, i -> R_i))};
        S/kernel map(R, S, M)
        )
    else if opts.Strategy === "4ti2" then (
        N := matrix transpose apply(J, I -> apply(#P.GroundSet, j -> if member(j, I) then 1 else 0));
        S/toricGroebner(N, S)
        )
    )

------------------------------------------
-- Derivative posets
------------------------------------------

closedInterval = method()
closedInterval (Poset, Thing, Thing) := Poset => (P, p, q) -> (
    if compare(P, p, q) then subposet(P, select(P.GroundSet, x -> compare(P, p, x) and compare(P, x, q)))
    else if compare(P, q, p) then subposet(P, select(P.GroundSet, x -> compare(P, q, x) and compare(P, x, p)))
    else error "The elements are incomparable."
    )

dilworthLattice = method()
dilworthLattice Poset := Poset => P -> (
    d := dilworthNumber P;
    G := select(maximalAntichains P, a -> #a == d);
    cmp := (A, B) -> all(A, a -> any(B, b -> compare(P, a, b)));
    Q := poset(G, cmp);
    Q.cache.isLowerSemilattice = true;
    Q.cache.isUpperSemimodular = true;
    Q.cache.connectedComponents = toList(0 ..< #Q.GroundSet);
    Q
    )

distributiveLattice = method()
distributiveLattice Poset := Poset => P -> (
    O := unique apply(P.GroundSet, p -> principalOrderIdeal(P, p));
    POI := poset(unique apply(subsets(#O), s -> sort unique flatten O_s), isSubset);
    POI.cache.OriginalPoset = P;
    POI.cache.isLowerSemilattice = true;
    POI.cache.isUpperSemimodular = true;
    POI.cache.connectedComponents = toList(0 ..< #P.GroundSet);
    POI
    )

-- The method dual is given in the Core and has options.
-- As we don't need the options, we discard them.
dual Poset := Poset => {} >> opts -> P -> (
    Q := poset(P.GroundSet, reverse \ P.Relations, transpose P.RelationMatrix);
    if P.cache.?connectedComponents then Q.cache.connectedComponents = P.cache.connectedComponents;
    if P.cache.?coveringRelations then Q.cache.coveringRelations = reverse \ P.cache.coveringRelations;
    if P.cache.?filtration then Q.cache.filtration = reverse P.cache.filtration;
    if P.cache.?greeneKleitmanPartition then Q.cache.greeneKleitmanPartition = P.cache.greeneKleitmanPartition;
    if P.cache.?isDistributive then Q.cache.isDistributive = P.cache.isDistributive;
    if P.cache.?isEulerian then Q.cache.isEulerian = P.cache.isEulerian;
    if P.cache.?isLowerSemilattice then Q.cache.isUpperSemilattice = P.cache.isLowerSemilattice;
    if P.cache.?isLowerSemimodular then Q.cache.isUpperSemimodular = P.cache.isLowerSemimodular;
    if P.cache.?isUpperSemilattice then Q.cache.isLowerSemilattice = P.cache.isUpperSemilattice;
    if P.cache.?isUpperSemimodular then Q.cache.isLowerSemimodular = P.cache.isUpperSemimodular;
    if P.cache.?maximalAntichains then Q.cache.maximalAntichains = P.cache.maximalAntichains;
    if P.cache.?maximalChains then Q.cache.maximalChains = reverse \ P.cache.maximalChains;
    if P.cache.?maximalElements then Q.cache.minimalElements = P.cache.maximalElements;
    if P.cache.?minimalElements then Q.cache.maximalElements = P.cache.minimalElements;
    if P.cache.?rankFunction then Q.cache.rankFunction = if (rk := P.cache.rankFunction) === null then null else (m := max rk; (i -> m - i) \ rk);
    Q
    )

filter = method()
filter (Poset, List) := List => (P, L) -> unique flatten apply(L, l -> principalFilter(P, l)) 

flagPoset = method()
flagPoset (Poset, List) := Poset => (P, L)-> (
    if not isRanked P then error "The poset must be ranked.";
    subposet(P, flatten (rankPoset P)_(sort unique L))
    )

indexLabeling = method()
indexLabeling Poset := Poset => P -> labelPoset(P, hashTable apply(#P.GroundSet, i -> P.GroundSet_i => i))

labelPoset = method()
labelPoset (Poset, HashTable) := Poset => (P, l) -> new Poset from {
    symbol GroundSet => (q -> l#q) \ P.GroundSet,
    symbol Relations => apply(P.Relations, r -> (q -> l#q) \ r),
    symbol RelationMatrix => P.RelationMatrix,
    symbol cache => new CacheTable from P.cache
    }

naturalLabeling = method()
naturalLabeling (Poset, ZZ) := Poset => (P, startIndex) -> (
    F := flatten filtration P;
    labelPoset(P, hashTable for i to #F - 1 list F_i => startIndex + i)
    )
naturalLabeling Poset := Poset => P -> naturalLabeling(P, 0)

openInterval = method()
openInterval (Poset, Thing, Thing) := Poset => (P, p, q) -> dropElements(closedInterval(P, p, q), {p, q})

orderIdeal = method()
orderIdeal (Poset, List) := List => (P, L) -> unique flatten apply(L, l -> principalOrderIdeal(P, l))

principalFilter = method()
principalFilter (Poset, Thing) := List => (P, a) -> P.GroundSet_(principalFilter'(P, indexElement(P, a)))

principalOrderIdeal = method()
principalOrderIdeal (Poset, Thing) := List => (P, a) -> P.GroundSet_(principalOrderIdeal'(P, indexElement(P, a)))

subposet = method()
subposet (Poset, List) := Poset => (P, L) -> dropElements(P, toList(set P.GroundSet - set L))

------------------------------------------
-- Operations
------------------------------------------
adjoinMax = method()
adjoinMax (Poset,Thing) := Poset => (P, a) -> (
    Q := poset(P.GroundSet | {a}, 
          P.Relations | apply(P.GroundSet, g-> {g,a}),
          matrix{{P.RelationMatrix, transpose matrix {toList (#P.GroundSet:1)}},{matrix {toList((#P.GroundSet):0)},1}});
    Q.cache.maximalElements = {#P.GroundSet - 1};
    if P.cache.?minimalElements then Q.cache.minimalElements = P.cache.minimalElements;
    Q
    )
adjoinMax Poset := Poset => P -> adjoinMax(P, 1 + max prepend(0, select(P.GroundSet, x-> class x === ZZ)))

adjoinMin = method()
adjoinMin (Poset,Thing) := Poset => (P, a) -> (
    Q := poset({a} | P.GroundSet, 
          apply(P.GroundSet, g -> {a,g}) | P.Relations,
          matrix{{1, matrix{toList (#P.GroundSet:1)}}, {transpose matrix {toList (#P.GroundSet:0)}, P.RelationMatrix}});
    Q.cache.minimalElements = {0};
    if P.cache.?maximalElements then Q.cache.maximalElements = P.cache.maximalElements;
    Q
    )
adjoinMin Poset := Poset => P -> adjoinMin(P, -1 + min prepend(1, select(P.GroundSet, x -> class x === ZZ)))

areIsomorphic = method()
areIsomorphic (Poset, List, Poset, List) := Boolean => (P, mu, Q, nu) -> isomorphism(P, mu, Q, nu) =!= null
areIsomorphic (Poset, Poset) := Boolean => (P, Q) -> isomorphism(P, Q) =!= null
Poset == Poset := areIsomorphic

augmentPoset = method()
augmentPoset (Poset, Thing, Thing) := Poset => (P, a, b) -> adjoinMin(adjoinMax(P, b), a)
augmentPoset Poset := Poset => P -> adjoinMin adjoinMax P

diamondProduct = method()
diamondProduct (Poset, Poset) := Poset => (P, Q)->(
    if isRanked P and isRanked Q then (
        P':=product(dropElements(P, minimalElements P),dropElements(Q, minimalElements Q));
        poset(prepend({first minimalElements P, first minimalElements Q}, P'.GroundSet), 
              join(apply(minimalElements P', p -> ({first minimalElements P, first minimalElements Q}, p)), P'.Relations))
    ) else error "The posets must be ranked."
    )

dropElements = method()
dropElements (Poset, List) := Poset => (P, L) -> (
    keptIndices := select(toList(0..#P.GroundSet-1), i -> not member(P.GroundSet#i, L));
    newGroundSet := P.GroundSet_keptIndices;
    newRelationMatrix := P.RelationMatrix_keptIndices^keptIndices;
    newRelations := select(allRelations(P, true), r -> not member(first r, L) and not member(last r, L));
    poset(newGroundSet, newRelations, newRelationMatrix)
    )
dropElements (Poset, Function) := Poset => (P, f) -> (
    keptIndices := select(toList(0 ..< #P.GroundSet), i-> not f(P.GroundSet#i));
    newGroundSet := P.GroundSet_keptIndices;
    newRelationMatrix := P.RelationMatrix_keptIndices^keptIndices;
    newRelations := select(allRelations(P, true), r -> not f(first r) and not f(last r));
    poset(newGroundSet, newRelations, newRelationMatrix)
    )
Poset - List := dropElements

-- Ported from Stembridge's Maple Package
isomorphism = method()
isomorphism (Poset, List, Poset, List) := HashTable => (P, mu, Q, nu) -> (
    -- Test for quick bail-out.
    if #coveringRelations P != #coveringRelations Q or #mu != #nu or any(#mu, i -> #mu#i != #nu#i) then return null;
    -- This relabels P, Q, mu, and nu so that the labels are guaranteed to be sensible.
    idxP := hashTable apply(#P.GroundSet, i -> P.GroundSet_i => i);
    P' := indexLabeling P;
    mu' := (S -> apply(S, p -> idxP#p)) \ mu;
    idxQ := hashTable apply(#Q.GroundSet, i -> Q.GroundSet_i => i);
    Q' := indexLabeling Q;
    nu' := (S -> apply(S, q -> idxQ#q)) \ nu;
    isom := isomorphism'(P', mu', Q', nu');
    -- This converts the isomorphism (if extant) back to P & Q relevancy.
    if isom === null then null else applyValues(applyKeys(isom, k -> P_k), v -> Q_v)
    )
isomorphism (Poset, Poset) := HashTable => (P, Q) -> isomorphism(P, {P.GroundSet}, Q, {Q.GroundSet})

-- Actual workhorse: Separated from base method.
-- Assumes P & Q are labeled sensibly (with integers).
isomorphism' = method()
isomorphism' (Poset, List, Poset, List) := HashTable => (P, mu, Q, nu) -> (
    -- 0. Check for non-partitions.
    mu' := flatten mu; 
    if #mu' != #P.GroundSet and isSubset(mu', P.GroundSet) then error "The list mu is not a partition of the ground set of P.";
    nu' := flatten nu;
    if #nu' != #Q.GroundSet and isSubset(nu', Q.GroundSet) then error "The list nu is not a partition of the ground set of Q.";
    -- 1. Do the graphs have incompatible vertex partitions or number of coveringRelations?
    if #coveringRelations P != #coveringRelations Q or #mu != #nu or any(#mu, i -> #mu#i != #nu#i) then return null;
    -- 2. Is there a lucky isomorphism?
    isom' := hashTable apply(mu', nu', (i, j) -> i => j);
    if isSubset(apply(coveringRelations P, r -> {isom'#(first r), isom'#(last r)}), coveringRelations Q) then return isom';
    -- 3. Partition the vertices of P and Q based on the number of in and out edges.
    cvrSep := (P, mu, q) -> (
        cp := partition(first, coveringRelations P);
        cvrby := apply(P.GroundSet, g -> if cp#?g then last \ cp#g else {});
        cp = partition(last, coveringRelations P);
        cvr := apply(P.GroundSet, g -> if cp#?g then first \ cp#g else {});
        mugrp := hashTable flatten apply(#mu, i -> apply(mu_i, p -> p => i));
        partition(first, apply(#P.GroundSet, i -> {sum(cvrby_i, j -> q^(-mugrp#j-1)) + sum(cvr_i, j -> q^(mugrp#j+1)), P.GroundSet_i}))
        );
    q := local q;
    R := ZZ(monoid[q, Inverses => true, MonomialOrder => Lex]);
    sepP := cvrSep(P, sort \ mu, R_0);
    sepQ := cvrSep(Q, sort \ nu, R_0);
    -- 4. Was the repartition non-trivial?  If so, recurse.
    kP := sort keys sepP;
    if kP =!= sort keys sepQ or any(keys sepP, k -> #sepP#k != #sepQ#k) then return null;
    mu' = apply(kP, k -> last \ sepP#k);
    nu' = apply(kP, k -> last \ sepQ#k);
    if #mu' > #mu then return isomorphism'(P, mu', Q, nu');
    -- 4a. Restrict P and Q to non-singleton sets.
    pp := partition(a -> #a == 1, mu');
    sisom := hashTable if pp#?true then (
        P = dropElements(P, flatten pp#true);
        mu' = pp#false;
        pq := partition(a -> #a == 1, nu');
        Q = dropElements(Q, flatten pq#true);
        nu' = pq#false;
        apply(flatten pp#true, flatten pq#true, (i, j) -> i => j)
        ) else {};
    -- 5. Break the smallest part of mu into a singleton and the rest.
    --    Check this against doing the same thing to nu in all possible ways.
    m := min apply(mu', a -> #a);
    j := position(mu', a -> #a == m);
    pick := (i, j, mu) -> join(take(mu, j), {{mu_j_i}, drop(mu_j, {i,i})}, take(mu, j+1-#mu));
    mu' = pick(0, j, mu');
    for i from 0 to m-1 do (
        isom' = isomorphism'(P, mu', Q, pick(i, j, nu'));
        if isom' =!= null then return merge(sisom, isom', (a,b) -> error "Something broke!");
        );
    null
    )
-- The product method is defined in the Core.
product (Poset, Poset) := Poset => (P, Q) -> 
    poset(flatten for p in P.GroundSet list for q in Q.GroundSet list {p, q},
          join(flatten for c in P.Relations list for q in Q.GroundSet list ({c_0, q}, {c_1, q}),
           flatten for c in Q.Relations list for p in P.GroundSet list ({p, c_0}, {p, c_1})))
Poset * Poset := product

removeIsomorphicPosets = method()
removeIsomorphicPosets List := List => L -> (
    if any(L, p -> not instance(p, Poset)) then error "The list must contain only Posets.";
    while #L > 0 list (
        p := first L;
        pp := partition(q -> p == q, drop(L, 1));
        L = if pp#?false then pp#false else {};
        p
        )
    )

union = method()
union (Poset, Poset) := Poset => (P, Q) -> poset(unique join(P.GroundSet, Q.GroundSet), unique join(P.Relations, Q.Relations))
Poset + Poset := union

------------------------------------------
-- Enumerators
------------------------------------------

booleanLattice = method()
booleanLattice ZZ := Poset => n -> (
    if n < 0 then n = -n; 
    if n == 0 then poset({""}, {}, matrix{{1}}) else (
        Bn1 := booleanLattice(n-1);
        G := apply(Bn1.GroundSet, p -> "0" | p) | apply(Bn1.GroundSet, p -> "1" | p);
        R := apply(Bn1.Relations, r -> {"0" | first r, "0" | last r}) | 
             apply(Bn1.Relations, r -> {"1" | first r, "1" | last r}) |
             apply(Bn1.GroundSet, p -> {"0" | p, "1" | p});
        M := matrix {{Bn1.RelationMatrix, Bn1.RelationMatrix}, {0, Bn1.RelationMatrix}};
        poset(G, R, M)
        )
    )

chain = method()
chain ZZ := Poset => n -> (
    if n == 0 then error "The integer n must be non-zero.";
    if n < 0 then n = -n;
    -- The matrix is known, so give it.
    poset(toList(1..n), apply(n-1, i -> {i+1, i+2}), matrix toList apply(1..n, i -> toList join((i-1):0, (n-i+1):1)))
    )

divisorPoset = method()
divisorPoset RingElement := Poset => m -> (
    if m == 0 then error "The RingElement m must be non-zero.";
    if #support m == 0 then return poset({m}, {}); -- Non-zero constants are special
    M := toList \ toList factor m;
    F := apply(M, m -> set apply(last m + 1, i -> (first m)^i));
    -- D is the set of all (positive) divisors of m
    D := sort if #F == 1 then toList first F else product \ toList@@deepSplice \ toList fold((a,b) -> a ** b, F);
    poset(D, (a,b) -> b % a == 0)
    )

divisorPoset ZZ := Poset => m -> (
    if m == 0 then error "The integer m must be non-zero.";
    if m < 0 then m = -m;
    if m == 1 then return poset({1}, {}); -- 1 is special
    M := toList \ toList factor m;
    F := apply(M, m -> set apply(last m + 1, i -> (first m)^i));
    -- D is the set of all (positive) divisors of m
    D := sort if #F == 1 then toList first F else product \ toList@@deepSplice \ toList fold((a,b) -> a ** b, F);
    poset(D, (a,b) -> b % a == 0)
    )

divisorPoset (RingElement, RingElement):= Poset =>(m, n) -> (
    if ring m === ring n then (
        if n % m === sub(0, ring m) then (
            P := divisorPoset (n//m);
            poset(apply(P.GroundSet, v -> v * m), apply(P.Relations, r -> {m * first r, m * last r}), P.RelationMatrix)
            ) else error "The first monomial does not divide the second."
        ) else error "The monomials must be in same ring."
    )

divisorPoset (List, List, PolynomialRing):= Poset => (m, n, R) -> (
    makeMonomialFromDegree := (R, d) -> product apply(numgens R, i-> R_i^(d#i));
    if #m === #n and #n === numgens R then divisorPoset(makeMonomialFromDegree(R, m), makeMonomialFromDegree(R, n))
    else error "Wrong number of variables in the first or the second exponent vector."
    )

dominanceLattice = method()
dominanceLattice ZZ := Poset => n -> (
    G := toList \ partitions n;
    cmp := (a, b) -> (
        if #b > #a then return false;
        sa := 0; 
        sb := 0;
        for k from 0 to #b - 1 do (
            sa = sa + a_k;
            sb = sb + b_k;
            if sa > sb then return false;
            );
        true
        );
    poset(G, cmp)
    )

facePoset = method()
facePoset SimplicialComplex := Poset => D -> poset(support \ flatten apply(toList(0..dim D), i -> toList flatten entries faces(i, D)), isSubset)

-- Hyperplane Arrangement Lattice: 
-- As written, this would most likely work for any type of arrangement lattice.
-- Given a set of linear forms defining the hyperplanes in the arrangement, returns set of intersection ideals.
--
-- Inputs:
--      L = equations defining hyperplanes
--      R = ring
-- Outputs: List of ideals of intersections, excluding the intersection of no hyperplanes and intersections which are empty.
hyperplaneEquivalence = method()
hyperplaneEquivalence (List,Ring) := List => (L,R) -> (
    allideals:=unique drop(apply(subsets L, h-> ideal gens gb ideal h),1);
    select(allideals, I-> not I == ideal(sub(1,R)))
    )

-- Inputs:
--      L = list of ideals produced by method hyperplaneEquivalence
--      R = ring
-- Outputs: Pairs of ideals (I,J), with I < J if J contains I
hyperplaneInclusions = method()
hyperplaneInclusions(List,Ring) := List => (L,R) -> (
    H:=apply(L, l-> sub(l,R));
    coverPairs:={};
    for l from 1 to #H-1 do
        for k to #H-1 do 
            if unique apply(flatten entries gens H_k, f-> f % gens H_l) === {sub(0,R)} then 
                coverPairs = append(coverPairs,{L_k,H_l});
    coverPairs
    )

-- Inputs:
--      L = equations defining arrangement
--      R = ring
-- Outputs: Intersection poset of hyperplane arrangement.
-- In theory, this should work on arrangements of hypersurfaces.  In practice, throws an error saying "antisymmetry fails."
intersectionLattice = method()
intersectionLattice (List, Ring) := Poset => (L, R)-> (
    G:=hyperplaneEquivalence(L,R);
    rel:=hyperplaneInclusions(G,R);
    poset(G,rel)
    )

lcmLattice = method( Options => { Strategy => 1 })
lcmLattice(MonomialIdeal) := Poset => opts -> (M) -> (
    L := flatten entries gens M;
    Ground := if opts.Strategy === 0 then prepend(1_(ring M), unique (lcm \ drop(subsets L, 1)))
              else apply(lcmLatticeProduceGroundSet L, D -> product apply(numgens ring M, i-> (ring M)_i^(D#i)));
    Rels := flatten for i to #Ground-1 list for j from i+1 to #Ground-1 list 
        if Ground_i % Ground_j == 0 then {Ground_j, Ground_i} else if Ground_j % Ground_i == 0 then {Ground_i, Ground_j} else continue;
    RelsMatrix := matrix apply(Ground, r -> apply(Ground, s -> if s % r == 0 then 1 else 0));
    poset (Ground, Rels, RelsMatrix)
    )
lcmLattice (Ideal) := Poset => opts -> (I) -> lcmLattice(monomialIdeal I, opts)

-- Used by lcmLattice for Strategy 1
protect next
lcmLatticeProduceGroundSet = G -> (
    degreeNextPair := (D, nextDegrees) -> hashTable {symbol degree => D, symbol next => nextDegrees};
    -- Builds the possible multidegrees by changes in variable i.
    determineLCMsForVariable := (lcmDegrees, i) -> (
        -- Takes the lcm of two degrees and determines which of the lowerNexts can later be joined to newDegree
        -- and change its multidegree. Note that the lower nexts are not all multi-degrees. 
        joinDegrees := (A,B, lowerNexts) ->  (
            C := max \ transpose {A.degree, B};
            degreeNextPair(C, select(lowerNexts, D -> any(C - D, i -> i < 0)))
            );
        newLCMDegrees := flatten apply(lcmDegrees, D -> (
            -- Take D's nexts are partition them by the exponent of the i-th variable. Store in P.
            P := partition(E -> E#i, D.next);
            -- Partition the possible degrees of the i-th variable into those that change multi-degree D 
            -- in the i-th coordinate and those that don't. Store in Q.
            Q := partition(d -> d > (D.degree)#i, keys P);
            --Restrict P to only those which change the degree the i-th variable of D.
            upperPartition := hashTable apply(if Q#?true then Q#true else {}, d -> d => P#d);
            -- The lowerNexts are those multi degrees that can change D in the indices larger than i, but not in i itself.
            lowerNexts := flatten apply(if Q#?false then Q#false else {}, d -> P#d);
            newD := degreeNextPair( D.degree, lowerNexts ); -- D with fewer nexts
            newMultiDegrees := flatten apply(keys upperPartition, d -> (
                lowerNexts = lowerNexts | upperPartition#d; -- build these as we go
                apply(upperPartition#d, E -> joinDegrees(D, E, lowerNexts))
                ));
            prepend(newD, newMultiDegrees)
            ));
        -- unique the multi-degrees list
        first \ values partition(D -> D.degree, select(newLCMDegrees, D -> D =!= null))
    );
    initialExps := flatten apply(G, m -> exponents m);
    n := if #initialExps === 0 then 0 else #(first initialExps);
    lcmDegrees := { degreeNextPair(apply(n, i -> 0), initialExps) };
    -- lcmDegrees contains all possible multi-degrees restricted to the first i varibles. For each of these multi-degrees
    -- we have a list of "nexts" which are atoms which could affect degrees of variables after i without changing the 
    -- degrees of variables before i.
    for i from 0 to n-1 do lcmDegrees = determineLCMsForVariable(lcmDegrees, i);
    sort apply(lcmDegrees, D -> D.degree)
    )

partitionLattice = method()
partitionLattice ZZ := Poset => n -> (
     L := toList (1..n);
     G := setPartition L;
     R := flatten apply(G, i-> partitionRefinementPairs i);
     poset(G,R)
     )

partitionRefinementPairs = method()
partitionRefinementPairs List := List => L-> (
    m := unique apply(L, l-> #l);
    M := local M;
    N := local N;
    MM := apply(m, i-> (symbol M)_i);
    NN := apply(m, i-> (symbol N)_i);
    for i in m do (
        subS := subsets toList(0 ..< i);
        M_i = take(subS,{1,#subS-2});
        N_i = unique apply(M_i, r-> sort {r, select(toList(0 ..< i), k-> not member(k,r))});
        );
    dropPart := apply(#L, i-> drop(L,{i,i}));
    coverSet := flatten for i from 0 to #L-1 list(
        splitPairs:=apply(N_(#L_i), m-> {(L_i)_(first m),(L_i)_(last m)});
        apply(splitPairs, j-> sort join(dropPart_i,j))
    );
    apply(coverSet, i -> {L,i})
    )

setPartition = method()
setPartition ZZ := List => n -> (
    L := {{{1}}};
    for i from 2 to n do (
        L = flatten for lambda in L list (
            lambdaparts := apply(#lambda, l-> for k to #lambda-1 list if k=!=l then lambda_k else continue);
            append(apply(#lambda, p-> lambdaparts_p | {lambda_p | {i}}), join(lambda,{{i}}))
            );
        );
    apply(L, sort)
    )
setPartition List := List => S -> (
    L := {{{first S}}};
    for s in drop(S,1) do (
        L = flatten for lambda in L list(
            dropPart := apply(#lambda, i-> drop(lambda,{i,i}));
            protoLevelSet := apply(#lambda, l-> join(dropPart_l,{lambda_l|{s}}));
            join(protoLevelSet, {lambda|{{s}}})
            );
        );
    apply(L,sort)
    )

-- Inputs:
--      L = equations defining (possibly nonprojective) arrangement
--      R = ring
-- Outputs: Intersection poset of projectivized hyperplane arrangement.
projectivizeArrangement = method()
projectivizeArrangement (List, Ring) := Poset => (L, R) -> (
    Z := local Z;
    S := (coefficientRing R)(monoid [append(gens R, Z)]);
    Z = last gens S;
    newL := apply(L, h->homogenize(sub(h,S), Z));
    G := hyperplaneEquivalence(newL,S);
    rel := hyperplaneInclusions(G,S);
    poset(G, rel)
    )

randomPoset = method(Options => {symbol Bias => 0.5})
randomPoset (List) := Poset => opts -> (G) -> (
    if not instance(opts.Bias, RR) and not instance(opts.Bias, QQ) and not instance(opts.Bias, ZZ) then error "The option Bias must be a ZZ, QQ, or RR.";
    b := if instance(opts.Bias, ZZ) then (
        if opts.Bias > 0 then 1.0/opts.Bias else error "The option Bias (as a ZZ) must be at least 1."
        ) else opts.Bias;
    if b < 0 or b > 1 then error "The option Bias must be at least 0 and at most 1.";
    poset(G, flatten for i from 0 to #G-1 list for j from i+1 to #G-1 list if random 1.0 < opts.Bias then {G_i, G_j} else continue)
    )
randomPoset (ZZ) := Poset => opts -> n -> randomPoset(toList(1..n), opts)

standardMonomialPoset = method()
standardMonomialPoset (MonomialIdeal, ZZ, ZZ) := Poset => (I, minDeg, maxDeg) -> poset(first entries basis(minDeg, maxDeg, quotient I), (m, n) -> n % m == 0)
standardMonomialPoset MonomialIdeal := Poset => I -> poset(first entries basis quotient I, (m, n) -> n % m == 0)

youngSubposet = method()
youngSubposet (List, List) := Poset => (lo, hi) -> (
    if min (drop(lo, -1) - drop(lo, 1)) < 0 or min (drop(hi, -1) - drop(hi, 1)) < 0 then error "The bounds must be weakly decreasing.";
    if #lo > #hi or any(#lo, i -> lo_i > hi_i) then error "The bounds are either incomparable or reversed.";
    allIncreases := (hi, L, i) -> if i == #hi then L else 
        allIncreases(hi, flatten if i == 0 then apply(L, d -> apply(toList(d_0..hi_0), j -> replace(0, j, d))) else
            apply(L, d -> apply(toList(d_i..min(hi_i, d_(i-1))), j -> replace(i, j, d))), i+1);
    G := apply(allIncreases(hi, {join(lo, toList((#hi-#lo):0))}, 0), d -> d_(positions(d, i -> i != 0)));
    poset(G, (a,b) -> #a <= #b and all(#a, i -> a_i <= b_i))
    )
youngSubposet List := Poset => hi -> youngSubposet({0}, hi)
youngSubposet ZZ := Poset => n -> (
    if n < 0 then n = -n;
    poset(toList \ flatten apply(n+1, i -> partitions i), (a,b) -> #a <= #b and all(#a, i -> a_i <= b_i))
    )

------------------------------------------
-- TeX & GAP
------------------------------------------

displayPoset = method(Options => { symbol SuppressLabels => posets'SuppressLabels, symbol PDFViewer => posets'PDFViewer, symbol Jitter => false })
displayPoset (Poset) := opts -> (P) -> (
    if not instance(opts.PDFViewer, String) then error "The option PDFViewer must be a string.";
    if not instance(opts.SuppressLabels, Boolean) then error "The option SuppressLabels must be a Boolean.";
    if not instance(opts.Jitter, Boolean) then error "The option Jitter must be a Boolean.";
    name := temporaryFileName();
    outputTexPoset(P, concatenate(name, ".tex"), symbol SuppressLabels => opts.SuppressLabels, symbol Jitter => opts.Jitter);
    run concatenate("pdflatex -output-directory /tmp ", name, " 1>/dev/null");
    run concatenate(opts.PDFViewer, " ", name,".pdf &");
    )

gapPosetConversion = method()
gapPosetConversion Poset := String => P -> (
    if not P.cache.?coveringRelations then coveringRelations P;
    cp := applyValues(partition(first, P.cache.coveringRelations), v -> (i -> 2 + last i) \ v);
    -- Note: Maximal elements are covered by a new element, m, in GAP (Simplicial Homology)
    m := #P.GroundSet + 2;
    cvrby := apply(#P.GroundSet, i -> if cp#?i then cp#i else {m});
    -- Note: Minimal elements cover a new element in GAP (Simplicial Homology)
    if not P.cache.?minimalElements then minimalElements P;
    toArray := L -> new Array from L;
    toString toArray (toArray \ join({apply(P.cache.minimalElements, i -> 2 + i)}, cvrby, {{}}))
    )
gapPosetConversion Array := Poset => A -> (
    A = toList \ (toList A);
    poset flatten apply(#A, p -> apply(A_p, q -> {p + 1, q}))
    )
gapPosetConversion String := Poset => S -> gapPosetConversion value S

outputTexPoset = method(Options => {symbol SuppressLabels => posets'SuppressLabels, symbol Jitter => false});
outputTexPoset (Poset,String) := String => opts -> (P,name) -> (
    if not instance(opts.SuppressLabels, Boolean) then error "The option SuppressLabels must be a Boolean.";
    if not instance(opts.Jitter, Boolean) then error "The option Jitter must be a Boolean.";
    fn := openOut name;
    fn << "\\documentclass[8pt]{article}"<< endl;
    fn << "\\usepackage{tikz}" << endl;
    fn << "\\newcommand{\\text}{\\mbox}" << endl;
    fn << "\\begin{document}" << endl;
    fn << "\\pagestyle{empty}" << endl << endl;
    fn << texPoset(P, opts) << endl;
    fn << "\\end{document}" << endl;
    close fn;
    get name
    )

texPoset = method(Options => {symbol SuppressLabels => posets'SuppressLabels, symbol Jitter => false})
texPoset (Poset) := String => opts -> (P) -> (
    if not instance(opts.SuppressLabels, Boolean) then error "The option SuppressLabels must be a Boolean.";
    if not instance(opts.Jitter, Boolean) then error "The option Jitter must be a Boolean.";
    -- edge list to be read into TikZ
    if not P.cache.?coveringRelations then coveringRelations P;
    edgelist := apply(P.cache.coveringRelations, r -> concatenate(toString first r, "/", toString last r));
    -- Find each level of P and set up the positioning of the vertices.
    if not P.cache.?filtration then filtration P;
    F := P.cache.filtration;
    levelsets := apply(F, v -> #v-1);
    scalew := min{1.5, 15 / (1 + max levelsets)};
    scaleh := min{2 / scalew, 15 / #levelsets};
    halflevelsets := apply(levelsets, lvl -> scalew * lvl / 2);
    spacings := apply(levelsets, lvl -> scalew * toList(0..lvl));
    -- The TeX String
    "\\begin{tikzpicture}[scale=1, vertices/.style={draw, fill=black, circle, inner sep=0pt}]\n" |
    concatenate(
        for i from 0 to #levelsets - 1 list for j from 0 to levelsets_i list
            {"\t\\node [vertices", if opts.SuppressLabels then "]" else (", label=right:{" | tex P.GroundSet_(F_i_j) | "}]"),
             " (",toString F_i_j,") at (-",toString halflevelsets_i,"+",
             toString ((if opts.Jitter then random(scalew*0.2) else 0) + spacings_i_j),",",toString (scaleh*i),"){};\n"}
        ) |
    concatenate("\\foreach \\to/\\from in ", toString edgelist, "\n\\draw [-] (\\to)--(\\from);\n\\end{tikzpicture}\n")
    )
-- Caveat: tex doesn't allow options to be passed.
tex Poset := texPoset

------------------------------------------
-- Vertices & vertex properties
------------------------------------------

atoms = method()
atoms Poset := List => P -> unique apply(select(coveringRelations P, R -> any(minimalElements P, elt -> (elt === R#0))), rels -> rels_1)

compare = method()
compare(Poset, Thing, Thing) := Boolean => (P, a, b) -> P.RelationMatrix_(indexElement(P, b))_(indexElement(P, a)) != 0

-- Ported from Stembridge's Maple Package
connectedComponents = method()
connectedComponents Poset := List => P -> (
    if not P.cache.?connectedComponents then (
        C := new MutableList from apply(toList(0 ..< #P.GroundSet), i -> {i});
        Q := toList(0 ..< #P.GroundSet);
        if not P.cache.?coveringRelations then coveringRelations P;
        cr := P.cache.coveringRelations;
        while (#cr > 0 and sum toList Q > 1) do (
            i := first first cr;
            j := last first cr; 
            C#j = unique join(C#i, C#j);
            cr = apply(drop(cr, 1), c -> { if c_0 == i then j else c_0, if c_1 == i then j else c_1 });
            Q = unique replace(position(Q, k -> k == i), j, Q);
            );
        P.cache.connectedComponents = (toList C)_Q;
        );
    apply(P.cache.connectedComponents, r -> P.GroundSet_r)
    )

-- Ported from Stembridge's Maple Package
-- F = filtration P; F_0 is the minimal elements of P, F_1 is the minimal elements of P-F_0, &c.
-- Notice that flatten filtration P is a linear extension of P.
filtration = method()
filtration Poset := List => P -> (
    if not P.cache.?filtration then (
        if not P.cache.?coveringRelations then coveringRelations P;
        cp := partition(last, P.cache.coveringRelations);
        cnt := new MutableList from apply(#P.GroundSet, i -> if cp#?i then #cp#i else 0);
        cp = partition(first, P.cache.coveringRelations);
        cvrby := apply(#P.GroundSet, i -> if cp#?i then last \ cp#i else {});
        neu := positions(cnt, c -> c == 0);
        ret := {neu} | while #neu != 0 list neu = for i in flatten cvrby_neu list if cnt#i == 1 then i else ( cnt#i = cnt#i - 1; continue );
        P.cache.filtration = drop(ret, -1);
        );
    apply(P.cache.filtration, lvl -> P.GroundSet_lvl)
    )

joinExists = method()
joinExists (Poset,Thing,Thing) := Boolean => (P, a, b) -> (
    OIa := principalFilter'(P, indexElement(P, a));
    OIb := principalFilter'(P, indexElement(P, b));
    upperBounds := toList (set(OIa)*set(OIb));
    if upperBounds == {} then false else (
        M := P.RelationMatrix;
        heightUpperBounds := flatten apply(upperBounds, i -> sum entries M_{i});
        #(select(heightUpperBounds, i-> i == min heightUpperBounds)) <= 1
        )
    )

joinIrreducibles = method()
joinIrreducibles Poset := List => P -> (
    if not isLattice P then error "The poset is not a lattice.";
    nonComparablePairs := select(subsets(P.GroundSet,2), posspair -> not compare(P, posspair#0,posspair#1) and not compare(P,posspair#1,posspair#0));
    joins := select(unique flatten apply(nonComparablePairs, posspair -> if joinExists(P, posspair#0, posspair#1) then posetJoin(P, posspair#0, posspair#1)), i -> i =!= null); 
    toList (set P.GroundSet - set joins)
    )

maximalElements = method()
maximalElements Poset := List => P -> (
    if not P.cache.?maximalElements then P.cache.maximalElements = select(#P.GroundSet, i -> all(#P.GroundSet, j -> P.RelationMatrix_(i,j) == 0 or i == j));
    P.GroundSet_(P.cache.maximalElements)
    )

meetExists = method()
meetExists (Poset, Thing, Thing) := Boolean => (P,a,b) -> (
    Fa := principalOrderIdeal'(P, indexElement(P, a));
    Fb := principalOrderIdeal'(P, indexElement(P, b));
    lowerBounds:= toList (set(Fa)*set(Fb));
    if lowerBounds == {} then false else (
        M := P.RelationMatrix;
        heightLowerBounds := flatten apply(lowerBounds, i -> sum entries M_{i});
        #(select(heightLowerBounds, i -> i == max heightLowerBounds)) <= 1
        )
    )

meetIrreducibles = method()
meetIrreducibles Poset := List => P -> (
    -- want to compute meets only for non-comparable elements
    if not isLattice P then error "The poset is not a lattice.";
    nonComparablePairs := select(subsets(P.GroundSet,2), posspair -> not compare(P, posspair#0,posspair#1) and not compare(P,posspair#1,posspair#0));
    meets := select(unique flatten apply(nonComparablePairs, posspair -> if meetExists(P, posspair#0, posspair#1) then posetMeet(P,posspair#0, posspair#1)), i -> i =!= null); 
    toList (set P.GroundSet - set meets)
    )

minimalElements = method()
minimalElements Poset := List => P -> (
    if not P.cache.?minimalElements then P.cache.minimalElements = select(#P.GroundSet, i -> all(#P.GroundSet, j -> P.RelationMatrix_(j,i) == 0 or i == j));
    P.GroundSet_(P.cache.minimalElements)
    )

posetJoin = method()     
posetJoin (Poset,Thing,Thing) := List => (P,a,b)  -> (
    OIa := principalFilter'(P, indexElement(P, a));     
    OIb := principalFilter'(P, indexElement(P, b));
    upperBounds := toList (set(OIa)*set(OIb));
    if upperBounds == {} then error "The elements do not share any upper bounds."
    else (
        M := P.RelationMatrix;
        heightUpperBounds := flatten apply(upperBounds, i -> sum entries M_{i});
        if #(select(heightUpperBounds, i -> i == min heightUpperBounds)) > 1 then error "The join does not exist; the least upper bound not unique." 
        else P.GroundSet_(upperBounds_{position (heightUpperBounds, l -> l == min heightUpperBounds)})
        )
    )

posetMeet = method()
posetMeet (Poset,Thing,Thing) := List => (P,a,b) ->(
    Fa := principalOrderIdeal'(P, indexElement(P, a));
    Fb := principalOrderIdeal'(P, indexElement(P, b));
    lowerBounds:= toList (set(Fa)*set(Fb));
    if lowerBounds == {} then error "The elements do not share any lower bounds."
    else (
        M := P.RelationMatrix;
        heightLowerBounds := flatten apply(lowerBounds, i -> sum entries M_{i});
        if #(select(heightLowerBounds, i -> i == max heightLowerBounds)) > 1 then error "The meet does not exist; the greatest lower bound not unique." 
        else P.GroundSet_(lowerBounds_{position (heightLowerBounds, l -> l == max heightLowerBounds)})
        )
    )

-- Ported from Stembridge's Maple Package
rankFunction = method()
rankFunction Poset := List => P -> (
    if P.cache.?rankFunction then return P.cache.rankFunction;
    rk := apply(#P.GroundSet, i -> {i, 0});
    if not P.cache.?coveringRelations then coveringRelations P;
    for r in P.cache.coveringRelations do (
        tmp := last rk#(r#1) - last rk#(r#0) - 1;
        if tmp == 0 then continue;
        u := first rk#(r#0);
        v := first rk#(r#1);
        if u == v then return P.cache.rankFunction = null;
        rk = if tmp > 0 then apply(rk, g -> if first g == u then {v, last g + tmp} else g) else
                              apply(rk, g -> if first g == v then {u, last g - tmp} else g);
        );
    P.cache.rankFunction = last \ rk
    )

-- Ranked:  There exists an integer ranking-function r on the groundset of P
--          such that for each x and y in P: if y covers x then r(y)-r(x) = 1.
rankPoset = method()
rankPoset Poset := List => P -> (
    rk := rankFunction P;
    if rk === null then error "The poset must be ranked.";
    rks := partition(i -> rk_i, 0 ..< #rk);
    apply(max rk + 1, r -> P.GroundSet_(toList (rks#r)))
    )

------------------------------------------
-- Relations & relation properties
------------------------------------------

allRelations = method()
allRelations (Poset, Boolean) := List => (P, NoLoops) -> (
    n := numrows P.RelationMatrix;
    offset := if NoLoops then 1 else 0;
    flatten for i to n - 1 list for j from i + offset to n - 1 list 
        if P.RelationMatrix_i_j == 1 then {P.GroundSet#j, P.GroundSet#i}
        else if P.RelationMatrix_j_i == 1 then {P.GroundSet#i, P.GroundSet#j}
        else continue
    )
allRelations Poset := List => P -> allRelations(P, false)

antichains = method()
antichains Poset := List => P -> sort unique flatten (subsets \ maximalAntichains P)
antichains (Poset, ZZ) := (P, k) -> sort unique flatten apply(maximalAntichains P, a -> subsets(a, k))

chains = method()
chains Poset := P -> sort unique flatten (subsets \ maximalChains P)
chains (Poset, ZZ) := (P, k) -> sort unique flatten apply(maximalChains P, c -> subsets(c, k))

coveringRelations = method()
coveringRelations Poset := List => P -> (
    if not P.cache.?coveringRelations then (
        gtp := for i to #P.GroundSet - 1 list for j to #P.GroundSet - 1 list if i != j and P.RelationMatrix_j_i != 0 then j else continue;
        P.cache.coveringRelations = flatten for i to #P.GroundSet - 1 list (
            gtgtp := unique flatten gtp_(gtp_i);
            apply(toList(set gtp_i - set gtgtp), j -> {i, j})
            );
        );
    apply(P.cache.coveringRelations, r -> P.GroundSet_r)
    )

flagChains = method()
flagChains (Poset,List) := List => (P, L) -> (
    if not isRanked P then error "The poset must be ranked.";
    rkP := rankPoset P;
    if #L == 0 then {} else if #L == 1 then apply(rkP_(first L), p -> {p}) else (
        L = sort L;
        flatten for c in flagChains(P, drop(L, 1)) list (
            for p in rkP_(first L) list if compare(P, p, first c) then prepend(p, c) else continue
            )
        )
    )

isAntichain = method()
isAntichain (Poset, List) := Boolean => (P, L) -> (
    Q := subposet(P, L);
    minimalElements Q === maximalElements Q
    )

-- Ported from Stembridge's Maple Package
linearExtensions = method()
linearExtensions Poset := List => P -> (
    linExtRec := (G, cr) -> (
        if #cr == 0 then permutations toList G else 
        flatten apply(toList (G - apply(cr, last)), m -> apply(linExtRec(G - {m}, select(cr, c -> first c =!= m)), e -> prepend(m, e)))
        );
    if not P.cache.?coveringRelations then coveringRelations P;
    le := linExtRec(set toList(0 ..< #P.GroundSet), P.cache.coveringRelations);
    apply(le, l -> P.GroundSet_l)
    )

maximalAntichains = method()
maximalAntichains Poset := List => P -> (
    if not P.cache.?maximalAntichains then (
        nonrelations := flatten for i from 0 to #P.GroundSet - 1 list for j from 0 to #P.GroundSet - 1 list
            if P.RelationMatrix_i_j == 0 and P.RelationMatrix_j_i == 0 then {i, j} else continue;
        cp := partition(first, nonrelations);
        cp = new HashTable from apply(#P.GroundSet, i -> i => if cp#?i then set(last \ cp#i) else set{});
        maxAntichains := apply(select(#P.GroundSet, i -> #cp#i == 0), i -> {i});
        nonMaxAntichains := apply(select(#P.GroundSet, i -> #cp#i != 0), i -> {i});
        while #nonMaxAntichains != 0 do
            nonMaxAntichains = unique flatten for a in nonMaxAntichains list (
                nonrelated := toList fold((i,j) -> i*j, apply(a, p -> cp#p));
                if #nonrelated == 0 then (maxAntichains = append(maxAntichains, a); continue)
                else apply(nonrelated, p -> sort append(a, p)));
        P.cache.maximalAntichains = maxAntichains;
        );
    apply(P.cache.maximalAntichains, a -> P.GroundSet_a)
    )

maximalChains = method()
maximalChains Poset := List => P -> (
    if not P.cache.?maximalChains then (
        if not P.cache.?minimalElements then minimalElements P;
        nonMaximalChains := apply(P.cache.minimalElements, i -> {i});
        if not P.cache.?coveringRelations then coveringRelations P;
        cp := partition(first, P.cache.coveringRelations);
        cvrby := hashTable apply(#P.GroundSet, i -> i => if cp#?i then last \ cp#i else {});
        maxChains := {};
        while #nonMaximalChains != 0 do 
            nonMaximalChains = flatten for c in nonMaximalChains list 
                if #cvrby#(last c) == 0 then (maxChains = append(maxChains, c); continue) else apply(cvrby#(last c), v -> append(c, v));
        P.cache.maximalChains = maxChains;
        );
    apply(P.cache.maximalChains, c -> P.GroundSet_c)
    )

------------------------------------------
-- Enumerative invariants
------------------------------------------

characteristicPolynomial = method(Options => {symbol VariableName => getSymbol "q"})
characteristicPolynomial Poset := RingElement => opts -> P -> (
    if not isRanked P then error "The poset must be ranked.";
    rk := rankFunction P;
    mu := moebiusFunction P;
    R := ZZ(monoid [opts.VariableName]);
    zeroP := first minimalElements P;
    sum(#P.GroundSet, i -> mu#(zeroP, P.GroundSet_i) * (R_0)^(max rk - rk#i))
    )

-- Following Stanley's definition in EC1
-- f_i * q_i_1 * ... * q_i_k (where i = (i_1, ..., i_k) is strictly increasing):
-- f_i is the number of chains of k vertices hitting ranks i.
flagfPolynomial = method(Options => {symbol VariableName => getSymbol "q"})
flagfPolynomial Poset := RingElement => opts -> P -> (
    if not isRanked P then error "The poset must be ranked.";
    rkP := #rankPoset P - 1;
    R := ZZ(monoid [opts.VariableName_0..opts.VariableName_(rkP)]);
    1 + sum for s in subsets toList(0..rkP) list #flagChains(P, s) * product(s, i -> R_i)
    )

-- Following Stanley's definition in EC1
flaghPolynomial = method(Options => {symbol VariableName => getSymbol "q"})
flaghPolynomial Poset := RingElement => opts -> P -> (
    if not isRanked P then error "The poset must be ranked.";
    ff := flagfPolynomial(P, opts);
    R := ring ff;
    fhp := product(gens R, r -> 1 - r) * sub(ff, apply(gens R, r -> r => r/(1 - r)));
    if denominator fhp == -1_R then -numerator fhp else numerator fhp
    )

-- f_i*q^i: f_i is the number of chains of i vertices in P
-- aka: chainPolynomial.
fPolynomial = method(Options => {symbol VariableName => getSymbol "q"})
fPolynomial Poset := RingElement => opts -> P -> (
    oP := orderComplex P;
    fV := fVector oP;
    R := ZZ(monoid [opts.VariableName]);
    sum(-1..dim oP, i -> fV#i * R_0^(i + 1))
    )

-- The union of k chains in P has maximum size equal to the 
-- sum of the first k terms in the Greene-Kleitman partition.
greeneKleitmanPartition = method(Options => {symbol Strategy => "antichains"})
greeneKleitmanPartition Poset := Partition => opts -> P -> (
    if P.cache.?greeneKleitmanPartition then return P.cache.greeneKleitmanPartition;
    (C, f) := if opts.Strategy === "chains" then (chains P, identity)
        else if opts.Strategy === "antichains" then (antichains P, conjugate)
        else error "The option Strategy must either be 'chains' or 'antichains'.";
    lambda := {};
    k := 0;
    while sum lambda < #P.GroundSet do (
        lk := max apply(subsets(C, k = k + 1), c -> #unique flatten c);
        lambda = append(lambda, lk - sum lambda);
        );
    f new Partition from lambda
    )

hPolynomial = method(Options => {symbol VariableName => getSymbol "q"})
hPolynomial Poset := RingElement => opts -> P -> (
    fp := fPolynomial(P, opts);
    R := ring fp;
    hp := (1-R_0)^(first degree fp) * sub(fp, R_0 => R_0 / (1 - R_0));
    if denominator hp == -1_R then -numerator hp else numerator hp
    )

moebiusFunction = method()
moebiusFunction Poset := HashTable => P -> (
    mu := new MutableHashTable;
    for i to #P.GroundSet-1 do (
        gtp := principalOrderIdeal'(P, i);
        for j to #P.GroundSet-1 do mu#(j, i) = if i === j then 1 else if not member(j, gtp) then 0 else -sum(gtp, z -> if mu#?(j, z) then mu#(j, z) else 0);
        );
    applyKeys(new HashTable from mu, (i, j) -> (P.GroundSet_i, P.GroundSet_j))
    )

-- r_i*x^i: r_i is the number of rank i vertices in P
rankGeneratingFunction = method(Options => {symbol VariableName => getSymbol "q"})
rankGeneratingFunction Poset := RingElement => opts -> P -> (
    if not isRanked P then error "The poset must be ranked.";
    R := ZZ(monoid [opts.VariableName]);
    sum(pairs tally rankFunction P, p -> p_1 * (R_0)^(p_0))
    )

-- zeta(i) = the number of weak-chains of i-1 vertices in P
zetaPolynomial = method(Options => {symbol VariableName => getSymbol "q"})
zetaPolynomial Poset := RingElement => opts -> P -> (
    oP := orderComplex P;
    fV := fVector oP;
    R := QQ(monoid [opts.VariableName]);
    X := toList(2..dim oP+2);
    Y := apply(X, n -> sum(2..n, i -> fV#(i-2) * binomial(n-2, i-2)));
    sum(#X, i -> Y_i * product(drop(X, {i,i}), xj -> (R_0 - xj)/(X_i-xj)))
    )

------------------------------------------
-- Properties
------------------------------------------

dilworthNumber = method()
dilworthNumber Poset := ZZ => P -> (
    if not P.cache.?maximalAntichains then maximalAntichains P;
    max apply(P.cache.maximalAntichains, a -> #a)
    )

-- The method height is given in the Core.
height Poset := ZZ => P -> (
    if not P.cache.?maximalChains then maximalChains P;
    -1 + max apply(P.cache.maximalChains, c -> #c)
    )

isAtomic = method()
isAtomic Poset := Boolean => P -> (
    if P.cache.?isAtomic then return P.cache.isAtomic;
    if not isLattice P then error "The poset must be a lattice.";
    if not P.cache.?coveringRelations then coveringRelations P;
    cp := partition(last, P.cache.coveringRelations);
    cvrs := apply(#P.GroundSet, i -> if cp#?i then first \ cp#i else {});
    P.cache.isAtomic = all(cvrs, cvr -> #cvr != 1 or cvrs#(first cvr) == {})
    )

isBounded = method()
isBounded Poset := Boolean => P -> #minimalElements P == 1 and #maximalElements P == 1

isConnected = method()
isConnected Poset := Boolean => P -> #connectedComponents P == 1

isDistributive = method()
isDistributive Poset := Boolean => P -> (
    if P.cache.?isDistributive then return P.cache.isDistributive;
    if not isLattice P then error "The poset must be a lattice.";
    P.cache.isDistributive = all(P.GroundSet, x -> 
        all(P.GroundSet, y -> 
            all(P.GroundSet, z -> 
                posetMeet(P, x, first posetJoin(P, y, z)) === posetJoin(P, first posetMeet(P, x, y), first posetMeet(P, x, z))
                )
            )
        )
    )

isEulerian = method()
isEulerian Poset := Boolean => P -> (
    if P.cache.?isEulerian then return P.cache.isEulerian;
    rk := rankFunction P;
    if rk === null then error "The poset must be ranked.";
    mu := moebiusFunction P;
    P.cache.isEulerian = all(#P.GroundSet, i -> all(principalOrderIdeal'(P, i), j -> mu#(P.GroundSet_j, P.GroundSet_i) == (-1)^(rk#j - rk#i)))
    )

isGeometric = method()
isGeometric Poset := Boolean => P -> (
    if not isLattice P then error "The poset must be a lattice.";
    isAtomic P and isUpperSemimodular P
    )

isGraded = method()
isGraded Poset := Boolean => P -> (
    if not P.cache.?maximalChains then maximalChains P;
    #unique apply(P.cache.maximalChains, c -> #c) == 1
    )

isLattice = method()
isLattice Poset := Boolean => P -> isLowerSemilattice P and isUpperSemilattice P 

isLowerSemilattice = method()
isLowerSemilattice Poset := Boolean => P -> if P.cache.?isLowerSemilattice then P.cache.isLowerSemilattice else
    P.cache.isLowerSemilattice = all(0 ..< #P.GroundSet, i -> all(i+1 ..< #P.GroundSet, j -> meetExists(P, P.GroundSet#i, P.GroundSet#j)))

-- Ported from Stembridge's Maple Package
isLowerSemimodular = method()
isLowerSemimodular Poset := Boolean => P -> (
    if P.cache.?isLowerSemimodular then return P.cache.isLowerSemimodular;
    if not isLattice P then error "The poset must be a lattice.";
    if not isRanked P then error "The poset must be ranked.";
    if not P.cache.?coveringRelations then coveringRelations P;
    cp := partition(last, P.cache.coveringRelations);
    cvrs := apply(#P.GroundSet, i -> if cp#?i then first \ cp#i else {});
    P.cache.isLowerSemimodular = all(#P.GroundSet, i -> all(#cvrs#i, j -> all(j, k -> #(set cvrs#(cvrs#i#j) * set cvrs#(cvrs#i#k)) === 1)))
    )

isModular = method()
isModular Poset := Boolean => P -> (
    if not isLattice P then error "The poset must be a lattice.";
    if not isRanked P then error "The poset must be ranked.";
    isLowerSemimodular P and isUpperSemimodular P
    )

isRanked = method()
isRanked Poset := Boolean => P -> rankFunction P =!= null

isSperner = method()
isSperner Poset := Boolean => P -> (
    rk := rankFunction P;
    if rk === null then error "The poset must be ranked.";
    maxrk := max values tally rk;
    maxrk == dilworthNumber P
    )

isStrictSperner = method()
isStrictSperner Poset := Boolean => P -> (
    if not isRanked P then error "The poset must be ranked.";
    rk := rankFunction P;
    rks := partition(i -> rk_i, 0 ..< #rk);
    ranks := sort \ apply(max rk + 1, r -> toList (rks#r));
    if not P.cache.?maximalAntichains then maximalAntichains P;
    ac := sort \ P.cache.maximalAntichains;
    #ranks == #ac and isSubset(ranks, ac)
    )

isUpperSemilattice = method()
isUpperSemilattice Poset := Boolean => P -> if P.cache.?isUpperSemilattice then P.cache.isLowerSemilattice else
    P.cache.isUpperSemilattice = all(0 ..< #P.GroundSet, i -> all(i+1 ..< #P.GroundSet, j -> joinExists(P, P.GroundSet#i, P.GroundSet#j)))

-- Ported from Stembridge's Maple Package
isUpperSemimodular = method()
isUpperSemimodular Poset := Boolean => P -> (
    if P.cache.?isUpperSemimodular then return P.cache.isUpperSemimodular;
    if not isLattice P then error "The poset must be a lattice.";
    if not isRanked P then error "The poset must be ranked.";
    if not P.cache.?coveringRelations then coveringRelations P;
    cp := partition(first, P.cache.coveringRelations);
    cvrby := apply(#P.GroundSet, i -> if cp#?i then last \ cp#i else {});
    P.cache.isUpperSemimodular = all(#P.GroundSet, i -> all(#cvrby#i, j -> all(j, k -> #(set cvrby#(cvrby#i#j) * set cvrby#(cvrby#i#k)) === 1)))
    )

------------------------------------------
------------------------------------------
-- Documentation
------------------------------------------
------------------------------------------

beginDocumentation()

-- Front Page
doc ///
    Key
        Posets
    Headline
        a package for working with partially ordered sets
    Description
        Text
            This package defines @TO "Poset"@ as a new data type and provides
            routines which use or produce posets.  A poset (partially ordered
            set) is a set together with a binary relation satisfying reflexivity,
            antisymmetry, and transitivity.
        Text
            @SUBSECTION "Contributors"@
            --
            The following people have generously contributed code to the package: 
            @HREF("http://www.math.cornell.edu/People/Grads/fisher.html","Kristine Fisher")@,
            @HREF("http://www.mathstat.dal.ca/~handrew/","Andrew Hoefel")@,
            @HREF("http://www.math.purdue.edu/~nkummini/","Manoj Kummini")@,
            @HREF("mailto:stephen.sturgeon\@uky.edu", "Stephen Sturgeon")@, and 
            @HREF("http://people.math.gatech.edu/~jyu67/Josephine_Yu/Main.html", "Josephine Yu")@.
        Text
            @SUBSECTION "Other acknowledgements"@
            --
            A few methods in this package have been ported from John Stembridge's Maple 
            package implementing posets, which is available at
            @HREF "http://www.math.lsa.umich.edu/~jrs/maple.html#posets"@.  
///

------------------------------------------
-- Data type & constructor
------------------------------------------

-- The Poset Type
doc ///
    Key
        Poset
        GroundSet
        RelationMatrix
        Relations
    Headline
        a class for partially ordered sets (posets)
    Description
        Text
            This class is a type of HashTable which represents finite posets.  It consists
            of a ground set, a list of relationships ${a,b}$ where $a \leq b$, and a matrix
            encoding these relations.
        Example
            G = {1,2,3,4};                  -- the ground set
            R = {{1,2},{1,3},{2,4},{3,4}};  -- a list of relations "generating" all relations
            P = poset(G, R)                 -- the poset with its relations matrix computed
    SeeAlso
        poset
///

-- _
doc ///
    Key
        (symbol _,Poset,ZZ)
    Headline
        returns an element of the ground set
    Usage
        a = P_i
    Inputs
        P:Poset
        i:ZZ
            index in the ground set
    Outputs
        a:Thing
            the $i$-th vertex in the ground set
    Description
        Text
            This method allows easy access to the vertices of the poset.
        Example
            P = booleanLattice 3;
            P_0
            P_3
    SeeAlso
        (symbol _,Poset,List)
        (symbol _*,Poset)
        Poset
///

doc ///
    Key
        (symbol _,Poset,List)
    Headline
        returns elements of the ground set
    Usage
        V = P_L
    Inputs
        P:Poset
        L:List
            indices in the ground set
    Outputs
        V:List
            the vertices indexed by $L$ in the ground set
    Description
        Text
            This method allows easy access to the vertices of the poset.
        Example
            P = booleanLattice 3;
            P_{2,4,5}
    SeeAlso
        (symbol _,Poset,ZZ)
        (symbol _*,Poset)
        Poset
///

-- symbol _*
doc ///
    Key
        (symbol _*,Poset)
    Headline
        returns the ground set of a poset
    Usage
        G = P_*
    Inputs
        P:Poset
    Outputs
        G:List
            the ground set of $P$
    Description
        Text
            This method allows easy access to ground set of a poset.
        Example
            P = booleanLattice 3;
            P_*
    SeeAlso
        (symbol _,Poset,ZZ)
        (symbol _,Poset,List)
        Poset
///

-- poset
doc ///
    Key
        poset
        (poset,List)
        (poset,List,Function)
        (poset,List,List)
        (poset,List,List,Matrix)
    Headline
        creates a new Poset object
    Usage
        P = poset R
        P = poset(G, cmp)
        P = poset(G, R)
        P = poset(G, R, M)
    Inputs
        G:List
            elements in the ground set of $P$
        R:List
            pairs {$a,b$} which indicate that $a \leq b$
        M:Matrix
            with entries $(i,j)$ equal to 1 if $G_j \leq G_i$ and 0 otherwise
        cmp:Function
            a binary function such that $cmp(G_i, G_j)$ is true if and only if $G_i \leq G_j$ in the partial order
    Outputs
        P:Poset
    Description
        Text
            This method creates a @TO "Poset"@ by defining the set and giving the order relations
            between the elements in the set.  The function assumes that each element in the
            ground set $G$ is distinct and operates by taking the transitive and reflexive closure
            of the relations in $R$.  The function returns an error if the input relations are
            incompatible with creating a poset.
        Example
            G = {a,b,c,d};
            R = {{a,b}, {a,c}, {c,d}};
            P = poset(G, R)
        Text
            It is unnecessary to pass the ground set if every vertex of the poset is a member
            of at least one relation in $R$.
        Example
            poset {{1,2},{2,3},{3,4}}
        Text
            Sometimes it is easier to create a poset by passing the ground set and a binary function
            which compares elements in the ground set.
        Example
            cmp = (a,b) -> b % a == 0;
            G = toList(1..10);
            P = poset(G, cmp)
        Text
            And, in other cases, it may be easy to find all relations in the poset.  In this case, if
            the matrix encoding all the relations is passed to the poset method, then it is not
            necessary to compute the transitive closure.  However, it should be noted that the method
            makes no checks on either the relations or the matrix in this case.
        Example
            S = QQ[x,y,z];
            G = {x^2, x*y, z^2, x^2*y*z, x*y*z^3, x^2*y^2*z^3};
            R = flatten for g in G list for h in G list if h %g == 0 then {g,h} else continue;
            M = matrix apply(G, g -> apply(G, h -> if h %g == 0 then 1 else 0));
            P = poset(G, R, M)
        Text
            In the previous example the vertices of the poset were @TO "RingElements"@.  In fact,
            the Posets package does not require the vertices to be of any particular type.  However,
            this also means when the package makes calls to external methods, it sometimes must
            relabel the vertices (usually to the index of the vertex in $G$).
    SeeAlso
        Poset
///

-- transitiveClosure
doc ///
    Key
        transitiveClosure
        (transitiveClosure,List,List)
    Headline
        computes the transitive closure of a set of relations
    Usage
        M = transitiveClosure(G, R)
    Inputs
        G:List
            the ground set
        R:List
            pairs {$a,b$} which indicate that $a \leq b$
    Outputs
        M:Matrix
            with entries $(i,j)$ equal to 1 if $G_j \leq G_i$ and 0 otherwise
    Description
        Text
            This method uses the @TO "floydWarshall"@ method from the @TO "Graphs"@ package
            to compute the @TO "RelationMatrix"@ from the relations $R$.
        Example
            G = {1,2,3,4,5};
            R = {{1,2}, {1,3}, {2,4}, {3,4}, {4,5}};
            transitiveClosure(G, R)
    SeeAlso
        poset
///

------------------------------------------
-- Derivative non-poset structures
------------------------------------------

-- comparabilityGraph
doc ///
    Key
        comparabilityGraph
        (comparabilityGraph,Poset)
    Headline
        produces the comparability graph of a poset
    Usage
        G = comparabilityGraph P
    Inputs
        P:Poset
    Outputs
        G:Graph
            which has an edge between two vertices if they are comparable in $P$
    Description
        Text
            The comparability graph of a poset $P$ is the @TO "Graph"@ with vertices given
            by the ground set of $P$ and which has edges between two vertices if
            they are comparable in $P$.
        Example
            comparabilityGraph booleanLattice 3
    Caveat
        This method renames the vertices with integers $0, 1, \ldots$ corresponding to the
        index of the vertices in the @TO "GroundSet"@.
    SeeAlso
        compare
        incomparabilityGraph
///

-- hasseDiagram
doc ///
    Key
        hasseDiagram
        (hasseDiagram,Poset)
    Headline
        produces the Hasse diagram of a poset
    Usage
        D = hasseDiagram P
    Inputs
        P:Poset
    Outputs
        D:Digraph
            which has the direct edge $(a,b)$ if and only if $a < b$ in $P$ and if
            $a \leq c \leq b$ then $c = a$ or $c = b$.
    Description
        Text
            The Hasse diagram of a poset is a @TO "Digraph"@ with vertices given by
            the ground set of $P$ and which has the direct edge $(a,b)$ if and only
            if $a < b$ in $P$ and there exists no $c$ such that $a < c < b$.
        Example
            hasseDiagram booleanLattice 3
    Caveat
        This method renames the vertices with integers $0, 1, \ldots$ corresponding to the
        index of the vertices in the @TO "GroundSet"@.
    SeeAlso
        coveringRelations
///

-- hibiIdeal
doc ///
    Key
        hibiIdeal
        (hibiIdeal,Poset)
        [hibiIdeal,CoefficientRing]
    Headline
        produces the Hibi ideal of a poset
    Usage
        H = hibiIdeal P
    Inputs
        P:Poset
        CoefficientRing=>Ring
            which specifies the coefficient ring of the @TO "PolynomialRing"@ $H$ is constructed in
    Outputs
        H:MonomialIdeal
            the Hibi ideal of $P$
    Description
        Text
            The Hibi ideal of $P$ is a @TO "MonomialIdeal"@ built over a ring in $2n$ variables
            $x_0, \ldots, x_{n-1}, y_0, \ldots, y_{n-1}$, where $n$ is the size of the ground set of $P$.  
            The generators of the ideal are in bijection with order ideals in $P$.  Let $I$ be 
            an order ideal of $P$.  Then the associated monomial is the product of the $x_i$ associated
            with members of $I$ and the $y_i$ associated with non-members of $I$.
        Example
            hibiIdeal chain 3
    SeeAlso
        hibiRing
        orderIdeal
        principalOrderIdeal
///

-- hibiRing
doc ///
    Key
        hibiRing
        (hibiRing,Poset)
        [hibiRing,CoefficientRing]
        [hibiRing,Strategy]
    Headline
        produces the Hibi ring of a poset
    Usage
        H = hibiRing P
        H = hibiRing(P, Strategy => "kernel")
        H = hibiRing(P, Strategy => "4ti2")
    Inputs
        P:Poset
        CoefficientRing=>Ring
            which specifies the coefficient ring of the @TO "PolynomialRing"@ $H$
        Strategy=>String
            which specifies whether to use Macaulay2's native @TO "kernel"@ method (Strategy => "kernel") or the package @TO "FourTiTwo"@ (Strategy => "4ti2")
    Outputs
        H:QuotientRing
            the toric algebra which is isomorphic to the Hibi ring of $P$
    Description
        Text
            The Hibi ring of $P$ is a monomial algebra generated by the monomials which generate the 
            Hibi ideal (@TO "hibiIdeal"@).  That is, the monomials built in $2n$ variables
            $x_0, \ldots, x_{n-1}, y_0, \ldots, y_{n-1}$, where $n$ is the size of the ground set of $P$.  
            The monomials are in bijection with order ideals in $P$.  Let $I$ be an order ideal of $P$.
            Then the associated monomial is the product of the $x_i$ associated with members of $I$ and 
            the $y_i$ associated with non-members of $I$.

            This method returns the toric quotient algebra isomorphic to the Hibi ring.  The ideal is
            the ideal of Hibi relations.  The generators of the @TO "PolynomialRing"@ $H$ is built
            over are of the form $t_I$ where $I$ is an order ideal of $P$.
        Example
            hibiRing booleanLattice 2
        Text
            The Hibi ring of the $n$ chain is just a polynomial ring in $n+1$ variables.
        Example
            hibiRing chain 4
        Text
            In some cases, it may be faster to use the @TO "FourTiTwo"@ method @TO "toricGroebner"@ to
            generate the Hibi relations.  Using the Strategy "4ti2" tells the method to use this approach.
        Example
            hibiRing(divisorPoset 6, Strategy => "4ti2")
    SeeAlso
        hibiIdeal
        orderIdeal
        principalOrderIdeal
        pPartitionRing
///

-- incomparabilityGraph
doc ///
    Key
        incomparabilityGraph
        (incomparabilityGraph,Poset)
    Headline
        produces the incomparability graph of a poset
    Usage
        G = incomparabilityGraph P
    Inputs
        P:Poset
    Outputs
        G:Graph
            which has an edge between two vertices if they are incomparable in $P$
    Description
        Text
            The comparability graph of a poset $P$ is the @TO "Graph"@ with vertices given
            by the ground set of $P$ and which has edges between two vertices if
            they are incomparable in $P$.
        Example
            incomparabilityGraph booleanLattice 3
    Caveat
        This method renames the vertices with integers $0, 1, \ldots$ corresponding to the
        index of the vertices in the @TO "GroundSet"@.
    SeeAlso
        comparabilityGraph
        compare
///

-- orderComplex
doc ///
    Key
        orderComplex
        (orderComplex,Poset)
        [orderComplex,VariableName]
        [orderComplex,CoefficientRing]
    Headline
        produces the order complex of a poset
    Usage
        O = orderComplex P
    Inputs
        P:Poset
        VariableName=>Symbol
        CoefficientRing=>Ring
    Outputs
        O:SimplicialComplex
            the order complex of $P$
    Description
        Text
            The order complex of a poset is the @TO "SimplicialComplex"@ with vertices
            corresponding to the ground set of $P$ and faces corresponding to the 
            @TO "chains"@ of $P$.
        Example
            orderComplex booleanLattice 3
        Text
            The minimal non-faces are given by the incomparable pairs of vertices
            in $P$.  Thus the order complex is the independence complex of the 
            @TO "incomparabilityGraph"@ of $P$ and the clique complex of the
            @TO "comparabilityGraph"@ of $P$.  Moreover, the facets are given
            by the @TO "maximalChains"@ of $P$.  Thus, the order complex of a 
            @TO "chain"@ poset is a simplex.
        Example
            orderComplex chain 5
    Caveat
        This method renames the vertices with integers $0, 1, \ldots$ corresponding to the
        index of the vertices in the @TO "GroundSet"@.
    SeeAlso
        chains
        comparabilityGraph
        incomparabilityGraph
        maximalChains
///

-- pPartitionRing
doc ///
    Key
        pPartitionRing
        (pPartitionRing,Poset)
        [pPartitionRing,CoefficientRing]
    Headline
        produces the p-partition ring of a poset
    Usage
        R = pPartitionRing P
        R = pPartitionRing(P, Strategy => "kernel")
        R = pPartitionRing(P, Strategy => "4ti2")
    Inputs
        P:Poset
        CoefficientRing=>Ring
        Strategy=>String
            which specifies whether to use Macaulay2's native @TO "kernel"@ method (Strategy => "kernel") or the package @TO "FourTiTwo"@ (Strategy => "4ti2")
    Outputs
        R:QuotientRing
            the toric algebra which is isomorphic to the $P$-partition ring
    Description
        Text
            Recall that a $P$-partition for a naturally labeled poset $P$ on
            vertices $1, \ldots, n$ is a function $f: P \rightarrow \mathbb{NN}$ which
            is order-reversing, i.e., if $i < j$ in $P$ then $f(i) \geq f(j)$ in $\mathbb{NN}$.
            To a $P$-partition $f$ we can assign the monomial $t_1^{f(1)} \ldots t_n^{f(n)}$.
            The $P$-partition ring is the ring spanned by the monomials corresponding
            to $P$-partitions.

            The $P$-partition ring is more simply generated by the monomials corresponding
            to the connected order ideals of $P$.  This method returns the toric quotient algebra,
            whose toric ideal is minimially generated, isomorphic to the $P$-partition ring.
        Example
            P = poset {{1,2}, {2,4}, {3,4}, {3,5}};
            pPartitionRing P
        Text
            In some cases, it may be faster to use the @TO "FourTiTwo"@ method @TO "toricGroebner"@ to
            generate the toric relations.  Using the Strategy "4ti2" tells the method to use this approach.
        Example
            pPartitionRing(divisorPoset 6, Strategy => "4ti2")
    SeeAlso
        hibiRing
        isConnected
        naturalLabeling
        orderIdeal
        principalOrderIdeal
///

------------------------------------------
-- Derivative posets
------------------------------------------

-- closedInterval
doc ///
    Key
        closedInterval
        (closedInterval,Poset,Thing,Thing)
    Headline
        computes the subposet contained between two points
    Usage
        I = closedInterval(P, p, q)
    Inputs
        P:Poset
        p:Thing
            an element of the poset
        q:Thing
            an element of the poset
    Outputs
        I:Poset
            the closed interval in $P$ between $p$ and $q$
    Description
        Text
            The closed interval between $p$ and $q$ is the subposet of $P$
            induced by the elements $z$ such that $p \leq z \leq q$.  If 
            $p$ and $q$ are incomparable, then an error is thrown.
        Example
            P = booleanLattice 3;
            closedInterval(P, "001", "111")
    SeeAlso
        openInterval
///

-- dilworthLattice
doc ///
    Key
        dilworthLattice
        (dilworthLattice,Poset)
    Headline
        computes the Dilworth lattice of a poset
    Usage
        D = dilworthLattice P
    Inputs
        P:Poset
    Outputs
        D:Poset
            the Dilworth lattice of $P$
    Description
        Text
            The Dilworth lattice of $P$ is the lattice of maximum length (the
            @TO "dilworthNumber"@) antichains in $P$.  Two such antichains have
            $A \leq B$ if and only if every member of $A$ is less than or equal
            (in $P$) to some member of $B$.
        Example
            P = poset {{0, 2}, {1, 2}, {1, 3}, {2, 5}, {3, 4}, {3, 5}};
            dilworthLattice P
    SeeAlso
        dilworthNumber
        maximalAntichains
///

-- distributiveLattice
doc ///
    Key
        distributiveLattice
        (distributiveLattice,Poset)
        OriginalPoset
    Headline
        computes the lattice of order ideals of a poset
    Usage
        L = distributiveLattice P
    Inputs
        P:Poset
    Outputs
        L:Poset
            the distributive lattice of $P$
    Description
        Text
            The distributive lattice of a poset $P$ is the poset of all order ideals
            of $P$ ordered by inclusion.  
        Example
            P = poset {{1,2}, {1,3}};
            distributiveLattice P
        Text
            The distributive lattice of a @TO "chain"@ poset of length $n$ is the
            chain poset of length $n+1$.
        Example
            distributiveLattice chain 3
    SeeAlso
        orderIdeal
///

-- dual
doc ///
    Key
        (dual,Poset)
    Headline
        produces the derived poset with relations reversed
    Usage
        P' = dual P
    Inputs
        P:Poset
    Outputs
        P':Poset
            the dual of $P$
    Description
        Text
            The dual of a poset is the poset on the same ground set
            but with all relations reversed. 
        Example
            P = divisorPoset 12;
            dual P
        Text
            Clearly then, the @TO "chain"@ posets and @TO "booleanLattice"@s
            are all self-dual.
        Example
            C = chain 5;
            areIsomorphic(C, dual C)
            B = booleanLattice 4;
            areIsomorphic(B, dual B)
///

-- filter
doc ///
    Key
        filter
        (filter,Poset,List)
    Headline
        computes the elements above given elements in a poset
    Usage
        F = filter(P, L)
    Inputs
        P:Poset
        L:List
            elements of the poset
    Outputs
        F:List
            containing all elements greater than at least one of the given elements 
    Description
        Text
            The filter of a given set of elements of a poset is all the 
            elements in the poset which are greater than at least one 
            of the elements in the given set. 
        Example
            P = booleanLattice 3;
            filter(P, {"001", "100"})
    SeeAlso
        orderIdeal
        principalFilter
        principalOrderIdeal
///

-- flagPoset
doc ///
    Key
        flagPoset
        (flagPoset,Poset,List)
    Headline
        computes the subposet of specified ranks of a ranked poset
    Usage
        F = flagPoset(P, L)
    Inputs
        P:Poset
        L:List
            containing rank indices
    Outputs
        F:Poset
            the subposet of $P$ of only the ranks specified in $L$
    Description
        Text
            The flag poset with respect to a list of rank indices
            is the subposet induced by the specified ranks.  The
            maximal chains of the flag poset can be computed with
            the @TO "flagChains"@ method.
        Example
            P = booleanLattice 4;
            rankFunction P
            flagPoset(P, {2,3})
            flagPoset(P, {1})
    SeeAlso
        flagChains
        isRanked
        rankPoset
///

-- indexLabeling
doc ///
    Key
        indexLabeling
        (indexLabeling,Poset)
    Headline
        relabels a poset with the labeling based on the indices of the vertices
    Usage
        Q = indexLabeling P
    Inputs
        P:Poset
    Outputs
        Q:Poset
    Description
        Text
            This method simply relabels the ground set of the poset
            based on the indices of the vertices.
        Example
            P = booleanLattice 3;
            Q = indexLabeling P;
            P.GroundSet
            Q.GroundSet
        Text
            Clearly, $P$ and $Q$ @TO "areIsomorphic"@.
        Example
            P == Q
        Text
            This can be useful for posets whose vertices have unruly names.
            Note the cache of $P$ is copied to the cache of $Q$ with the
            appropriate adjustments being made.
    SeeAlso
        (symbol _, Poset, ZZ)
        (symbol _, Poset, List)
        labelPoset
        naturalLabeling
///

-- labelPoset
doc ///
    Key
        labelPoset
        (labelPoset,Poset,HashTable)
    Headline
        relabels a poset with the specified labeling
    Usage
        Q = labelPoset(P, l)
    Inputs
        P:Poset
        l:HashTable
            with $P.GroundSet$ as the keys and the new labels as the values
    Outputs
        Q:Poset
            a poset isomorphic to $P$
    Description
        Text
            This method simply relabels the ground set of the poset
            based on givne labeling.
        Example
            P = chain 5;
            l = hashTable { 1 => a, 2 => b, 3 => c, 4 => d, 5 => e};
            Q = labelPoset(P, l);
            P.GroundSet
            Q.GroundSet
        Text
            Clearly, $P$ and $Q$ @TO "areIsomorphic"@.
        Example
            P == Q
    SeeAlso
        (symbol _, Poset, ZZ)
        (symbol _, Poset, List)
        indexLabeling
        isomorphism
        naturalLabeling
///

-- naturalLabeling
doc ///
    Key
        naturalLabeling
        (naturalLabeling,Poset)
        (naturalLabeling,Poset,ZZ)
    Headline
        relabels a poset with a natural labeling
    Usage
        Q = naturalLabeling P
        Q = naturalLabeling(P, startIndex)
    Inputs
        P:Poset
        startIndex:ZZ
            the starting index from which the poset is relabeled (default 0)
    Outputs
        Q:Poset
    Description
        Text
            A poset is naturally labeled if the ground set is ordered
            $v_1, \ldots, v_n$ and if $v_i \leq v_j$ in $P$ implies
            $i \leq j$.  This method relabels the ground set of the
            poset (suppose it has $n$ vertices) to be $0, 1, \ldots, n-1$.
        Example
            P = booleanLattice 3;
            Q = naturalLabeling P
            all(allRelations Q, r -> r_0 <= r_1)
        Text
            If @TT "startIndex"@ is specified, then the values are shifted
            by that amount.  This can be useful for making a disjoint
            union of posets.
        Example
            C = chain 3;
            Q' = sum(3, i -> naturalLabeling(C, 3*i))
            all(allRelations Q', r -> r_0 <= r_1)
        Text
            Note the cache of $P$ is copied to the cache of $Q$ with the
            appropriate adjustments being made.
    SeeAlso
        filtration
        indexLabeling
        labelPoset
///

-- openInterval
doc ///
    Key
        openInterval
        (openInterval,Poset,Thing,Thing)
    Headline
        computes the subposet contained strictly between two points
    Usage
        I = openInterval(P, a, b)
    Inputs
        P:Poset
        a:Thing
            an element of the poset
        b:Thing
            an element of the poset
    Outputs
        I:Poset
            the open interval in $P$ between $a$ and $b$
    Description
        Text
            The closed interval between $a$ and $b$ is the subposet of $P$
            induced by the elements $z$ such that $p < z < q$.  If 
            $a$ and $b$ are incomparable, then an error is thrown.
        Example
            P = booleanLattice 3;
            openInterval(P, "001", "111")
    SeeAlso
        closedInterval
///

-- orderIdeal
doc ///
    Key
        orderIdeal
        (orderIdeal,Poset,List)
    Headline
        computes the elements above given elements in a poset
    Usage
        I = orderIdeal(P, L)
    Inputs
        P:Poset
        L:List
            elements of the poset
    Outputs
        I:List
            containing all elements greater than at least one of the given elements 
    Description
        Text
           The filter of a given set of elements of a poset is all the 
           elements in the poset which are greater than at least one 
           of the elements in the given set. 
        Example
            P = booleanLattice 3;
            orderIdeal(P, {"001", "100"})
    SeeAlso
        filter
        principalFilter
        principalOrderIdeal
///

-- principalFilter
doc ///
    Key
        principalFilter
        (principalFilter,Poset,Thing)
    Headline
        computes the elements above a given element in a poset
    Usage
        F = principalFilter(P, a)
    Inputs
        P:Poset
        a:Thing
            an element of the poset
    Outputs
        F:List
            containing all elements greater than the given element
    Description
        Text
            The filter of a given element of a poset is all the
            elements in the poset which are greater than the element.
        Example
            P = booleanLattice 3;
            principalFilter(P, "101")
    SeeAlso
        filter
        orderIdeal
        principalOrderIdeal
///

-- principalOrderIdeal
doc ///
    Key
        principalOrderIdeal
        (principalOrderIdeal,Poset,Thing)
    Headline
        computes the elements below a given element in a poset
    Usage
        I = principalOrderIdeal(P, a)
    Inputs
        P:Poset
        a:Thing
            an element of the poset
    Outputs
        I:List
            containing all elements less than the given elements
    Description
        Text
            The order ideal of a element of a poset is all the
            elements in the poset which are less than the given element.
        Example
            P = booleanLattice 3;
            principalOrderIdeal(P, "101")
    SeeAlso
        filter
        orderIdeal
        principalFilter
///

-- subposet
doc ///
    Key
        subposet
        (subposet,Poset,List)
    Headline
        computes the induced subposet of a poset given a list of elements
    Usage
        Q = subposet(P, L)
    Inputs
        P:Poset
        L:List
            containing elements in the poset
    Outputs
        Q:Poset
            the induced subposet of $P$ with ground set $L$
    Description
        Text
            The induced subposet $Q$ on ground set $L$ of a poset $P$ has
            a partial order induced by the partial order on $P$.
        Example
            C = chain 7;
            subposet(C, {2,3,5,6})
    SeeAlso
        dropElements
        poset
///

------------------------------------------
-- Operations
------------------------------------------

-- adjoinMax
doc ///
    Key
        adjoinMax
        (adjoinMax,Poset)
        (adjoinMax,Poset,Thing)
    Headline
        computes the poset with a new maximum element
    Usage
        Q = adjoinMax P
        Q = adjoinMax(P, a)
    Inputs
        P:Poset
        a:Thing
            the new maximal element of $P$
    Outputs
        Q:Poset
    Description
        Text
            This method simply creates a new poset $Q$ with the maximal
            element $a$.  If $a$ is unspecified, $1$ or $1$ more than
            the largest integer vertex is used.
        Example
            P = poset {{1,2},{1,3},{1,4}};
            adjoinMax(P, 100)
    SeeAlso
        adjoinMin
        augmentPoset
///

-- adjoinMin
doc ///
    Key
        adjoinMin
        (adjoinMin,Poset)
        (adjoinMin,Poset,Thing)
    Headline
        computes the poset with a new minimum element
    Usage
        Q = adjoinMin P
        Q = adjoinMin(P, a)
    Inputs
        P:Poset
        a:Thing
            the new minimal element of $P$
    Outputs
        Q:Poset
    Description
        Text
            This method simply creates a new poset $Q$ with the minimal
            element $a$.  If $a$ is unspecified, the element $0$ or $1$
            less than the smallest integer vertex is used.
        Example
            P = poset {{1,4},{2,4},{3,4}};
            adjoinMin(P, 0)
    SeeAlso
        adjoinMax
        augmentPoset
///

-- areIsomorphic
doc ///
    Key
        areIsomorphic
        (areIsomorphic,Poset,List,Poset,List)
        (areIsomorphic,Poset,Poset)
        (symbol ==,Poset,Poset)
    Headline
        determines if two posets are isomorphic
    Usage
        r = areIsomorphic(P, Q)
        r = areIsomorphic(P, mu, Q, nu)
        r = P == Q
    Inputs
        P:Poset
        mu:List
            a partition of the ground set of $P$ into classes
        Q:Poset
        nu:List
            a partition of the ground set of $Q$ into classes
    Outputs
        r:Boolean
            whether $P$ and $Q$ are isomorphic as posets
    Description
        Text
            Two posets are isomorphic if there is a partial order
            preserving bijection between the ground sets of the posets
            which preserves the specified ground set partitions.

            If $mu$ and $nu$ are not specified, then the trivial partitions
            (the entire ground set in a single part) are used.
        Example
            C = chain 5;
            P = poset {{a,b},{b,c},{c,d},{d,e}};
            areIsomorphic(C, P)
        Text
            The product of $n$ chains of length $2$ is isomorphic to
            the boolean lattice on $n$ elements.  These are also
            isomorphic to the divisor lattice on the product of $n$ distinct primes.
        Example
            B = booleanLattice 5;
            B == product(5, i -> chain 2)
            B == divisorPoset (2*3*5*7*11)
            B == divisorPoset (2^2*3*5*7)
        Text
            This method uses the method @TO "isomorphism"@, which was ported
            from John Stembridge's Maple package available at
            @HREF "http://www.math.lsa.umich.edu/~jrs/maple.html#posets"@.  
    SeeAlso
        isomorphism
        removeIsomorphicPosets
///

-- augmentPoset
doc ///
    Key
        augmentPoset
        (augmentPoset,Poset)
        (augmentPoset,Poset,Thing,Thing)
    Headline
        computes the poset with an adjoined minimum and maximum
    Usage
        Q = augmentPoset P
        Q = augmentPoset(P, a, b)
    Inputs
        P:Poset
        a:Thing
            the new minimal element of $P$
        b:Thing
            the new maximal element of $P$
    Outputs
        Q:Poset
    Description
        Text
            This method simply creates a new poset $Q$ with the minimal
            element $a$ and the maximal element $b$.  If $a$ and $b$ are
            unspecified, the elements $0$ and $1$ are used, respectively.
    SeeAlso
        adjoinMax
        adjoinMin
///

-- diamondProduct
doc ///
    Key
        diamondProduct
        (diamondProduct,Poset,Poset)
    Headline
        computes the diamond product of two ranked posets
    Usage
        D = diamondProduct(P, Q)
    Inputs
        P:Poset
            which is ranked
        Q:Poset
            which is ranked
    Outputs
        D:Poset
    Description
        Text
            The diamond product of two ranked posets is the cartesian 
            product of the posets with their minimal elements removed
            and a new minimal element adjoined to the product.
        Example
            diamondProduct(chain 3, chain 3)
    SeeAlso
        isRanked
        product
///

-- dropElements
doc ///
    Key
        dropElements
        (dropElements,Poset,Function)
        (dropElements,Poset,List)
        (symbol -,Poset,List)
    Headline
        computes the induced subposet of a poset given a list of elements to remove
    Usage
        Q = dropElements(P, f)
        Q = dropElements(P, L)
        Q = P - L
    Inputs
        P:Poset
        L:List
            containing elements of $P$ to remove
        f:Function
            which returns true for elements to remove and false otherwise
    Outputs
        Q:Poset
    Description
        Text
            This method computes the induced subposet $Q$ of $P$ with the
            elements of $L$ removed from the poset.
        Example
            P = chain 5;
            dropElements(P, {3})
            P - {4, 5}
        Text
            Alternatively, this method computes the induced subposet $Q$
            of $P$ with the elements removed which return true when 
            $f$ is applied.
        Example
            P = divisorPoset (2*3*5*7);
            Q = dropElements(P, e -> e % 3 == 0)
            Q == divisorPoset(2*5*7)
    SeeAlso
        subposet
///

-- isomorphism
doc ///
    Key
        isomorphism
        (isomorphism,Poset,Poset)
        (isomorphism,Poset,List,Poset,List)
    Headline
        computes an isomorphism between isomorphic posets
    Usage
        pi' = isomorphism(P, Q)
        pi' = isomorphism(P, mu, Q, nu) 
    Inputs
        P:Poset
        mu:List
            a partition of the ground set of $P$ into classes
        Q:Poset
        nu:List
            a partition of the ground set of $Q$ into classes
    Outputs
        pi':HashTable
            which specifies a partial order preserving bijection 
            from the ground set of $P$ to the ground set of $Q$
    Description
        Text
            Two posets are isomorphic if there is a partial order
            preserving bijection between the ground sets of the posets
            which preserves the specified ground set partitions.

            If $mu$ and $nu$ are not specified, then the trivial partitions
            (the entire ground set in a single part) are used.
        Example
            isomorphism(divisorPoset (2*3*5), booleanLattice 3)
        Text
            This method was ported from John Stembridge's Maple package available at
            @HREF "http://www.math.lsa.umich.edu/~jrs/maple.html#posets"@.  
    SeeAlso
        areIsomorphic
        removeIsomorphicPosets
///

-- product
doc ///
    Key
        (product,Poset,Poset)
        (symbol *,Poset,Poset)
    Headline
        computes the product of two posets
    Usage
        R = product(P, Q)
        R = P * Q
    Inputs
        P:Poset
        Q:Poset
    Outputs
        R:Poset
            the cartesian product of $P$ and $Q$
    Description
        Text
            The cartesian product of the posets $P$ and $Q$ is the 
            new poset whose ground set is the cartesian product of
            the ground sets of $P$ and $Q$ and with partial order
            given by $(a,b) \leq (c,d)$ if and only if $a \leq c$
            and $b \leq d$.
        Example
            product(chain 3, poset {{a,b},{b,c}})
        Text
            The product of $n$ chains of length $2$ is isomorphic to
            the boolean lattice on $n$ elements.  These are also
            isomorphic to the divisor lattice on the product of $n$ distinct primes.
        Example
            B = booleanLattice 5;
            B == product(5, i -> chain 2)
            B == divisorPoset (2*3*5*7*11)
            B == divisorPoset (2^2*3*5*7)
    SeeAlso
        diamondProduct
///

-- removeIsomorphicPosets
doc ///
    Key
        removeIsomorphicPosets
        (removeIsomorphicPosets,List)
    Headline
        returns a sub-list of non-isomorphic posets
    Usage
        N = removeIsomorphicPosets L
    Inputs
        L:List
            containing posets
    Outputs
        N:List
            containing posets with non-isomorphic elements
    Description
        Text
            This method returns a sublist $N$ of $L$ containing the 
            elements of $L$, in order, where the first instance of
            each isomorphism class is retained.
        Example
            L = {chain 4, divisorPoset (2^3), booleanLattice 3, booleanLattice 2, product(3, i -> chain 2)};
            removeIsomorphicPosets L
        Text
            This method uses the method @TO "isomorphism"@, which was ported
            from John Stembridge's Maple package available at
            @HREF "http://www.math.lsa.umich.edu/~jrs/maple.html#posets"@.  
    SeeAlso
        Posets
///

-- union
doc ///
    Key
        union
        (union,Poset,Poset)
        (symbol +,Poset,Poset)
    Headline
        computes the union of two posets
    Usage
        R = union(P, Q)
        R = P + Q
    Inputs
        P:Poset
        Q:Poset
    Outputs
        R:Poset
            the union of $P$ and $Q$
    Description
        Text
            The union of two posets is the poset induced by the union
            of the ground sets and the covering relations.
        Example
            union(chain 3, poset {{1,4},{4,5},{5,3}})
    SeeAlso
        product
///

------------------------------------------
-- Enumerators
------------------------------------------

-- booleanLattice
doc ///
    Key
        booleanLattice
        (booleanLattice,ZZ)
    Headline
        generates the boolean lattice on $n$ elements
    Usage
        B = booleanLattice n
    Inputs
        n:ZZ
    Outputs
        B:Poset
    Description
        Text
            The boolean lattice on $n$ elements is the poset of
            binary strings of length $n$ with order given by
            componentwise ordering.  
        Example
            n = 3;
            B = booleanLattice n
        Text
            It can also be seen as the poset of subsets of a set
            of $n$ elements with order given by containment.
        Example
            B == poset(subsets n, isSubset)
        Text
            It is also the $n$-fold product of the @TO "chain"@
            of length $2$.
        Example
            B == product(n, i -> chain 2)
        Text
            Further, it is the @TO "divisorPoset"@ of the 
            product of $n$ distinct primes.
        Example
            B == divisorPoset (2*3*5)
    SeeAlso
        chain
        divisorPoset
///

-- chain
doc ///
    Key
        chain
        (chain,ZZ)
    Headline
        generates the chain poset on $n$ elements
    Usage
        C = chain n
    Inputs
        n:ZZ
            the length of the chain
    Outputs
        C:Poset
    Description
        Text
            The chain poset on $n$ elements is the total
            order on the integers $1..n$.
        Example
            n = 5;
            C = chain n
            C == poset(toList(1..n), (a,b) -> a <= b)
        Text
            It is also the @TO "divisorPoset"@ of a prime
            $p$ to the $n-1$ power.
        Example
            C == divisorPoset(2^(n-1))
    SeeAlso
        divisorPoset
///

-- divisorPoset
doc ///
    Key
        divisorPoset
        (divisorPoset,ZZ)
    Headline
        generates the poset of divisors
    Usage
        P = divisorPoset n
    Inputs
        n:ZZ
            which is not zero
    Outputs
        P:Poset
    Description
        Text
            The divisor poset of an integer is the poset
            of positive divisors of an integer $n$ with order
            induced by divisibility.
        Example
            divisorPoset 12
            divisorPoset 30
    SeeAlso
        (divisorPoset,RingElement)
        (divisorPoset,RingElement,RingElement)
        (divisorPoset,List,List,PolynomialRing)
///

doc ///
    Key
        (divisorPoset,RingElement)
    Headline
        generates the poset of divisors
    Usage
        P = divisorPoset m
    Inputs
        m:RingElement
            which is a polynomial
    Outputs
        P:Poset
    Description
        Text
            The divisor poset of a polynomial $m$ is the
            poset of divisors with order induced by
            divisibility.
        Example
            R = QQ[x,y];
            divisorPoset(x^2*y)
        Text
            The method works with non-monomial divisors as well.
        Example
            divisorPoset(x*y^2 - 2*x*y + x)
    SeeAlso
        divisorPoset
        (divisorPoset,ZZ)
        (divisorPoset,RingElement,RingElement)
        (divisorPoset,List,List,PolynomialRing)
///

doc ///
    Key
        (divisorPoset,RingElement,RingElement)
    Headline
        generates the poset of divisors with a lower and upper bound
    Usage
        P = divisorPoset(m, n)
    Inputs
        m:RingElement
            the lower bound, which divides $n$
        n:RingElement
            the upper bound, which is a multiple of $m$
    Outputs
        P:Poset
    Description
        Text
            This method generates the divisor poset of $n$ with
            elements which are multiples of $n$.
        Example
            R = QQ[x,y];
            divisorPoset(x*y-x, x^2*y^2 - 2*x^2*y + x^2)
    SeeAlso
        divisorPoset
        (divisorPoset,ZZ)
        (divisorPoset,RingElement)
        (divisorPoset,List,List,PolynomialRing)
///

doc ///
    Key
        (divisorPoset,List,List,PolynomialRing)
    Headline
        generates the poset of divisors
    Usage
        P = divisorPoset(m, n, R)
    Inputs
        m:List
            an exponent vector of the lower bound monomial in $R$
        n:List
            an exponent vector of the upper bound monomial in $R$
        R:PolynomialRing
    Outputs
        P:Poset
    Description
        Text
            This method generates the divisor poset of the monomials in $R$
            whose exponent vectors are given by $m$ and $n$.
        Example
            R = QQ[x,y];
            D = divisorPoset({0,1}, {2,2}, R)
            D == divisorPoset(y, x^2*y^2)
    SeeAlso
        divisorPoset
        (divisorPoset,ZZ)
        (divisorPoset,RingElement)
        (divisorPoset,RingElement,RingElement)
///

-- dominanceLattice
doc ///
    Key
        dominanceLattice
        (dominanceLattice,ZZ)
    Headline
        generates the dominance lattice of partitions of $n$
    Usage
        P = dominanceLattice n
    Inputs
        n:ZZ
    Outputs
        P:Poset
    Description
        Text
            The dominance lattice of partitons of $n$ is the
            lattice of partitons of $n$ under the dominance
            ordering.  Suppose $p$ and $q$ are two partitions
            of $n$.  Then $p$ is less than or equal to $q$
            if and only if the $k$-th partial sum of $p$
            is at most the $k$-th partial sum of $q$, where
            the partitions are extended with zeros, as needed.
        Example
            D = dominanceLattice 6;
            closedInterval(D, {2,2,1,1}, {4,2})
        Text
            For $n \leq 5$, the dominance lattice of $n$ is
            isomorphic to an appropriately long chain poset.
        Example
            dominanceLattice 2 == chain 2
            dominanceLattice 3 == chain 3
            dominanceLattice 4 == chain 5
            dominanceLattice 5 == chain 7
    SeeAlso
        partitionLattice
        partitions
        youngSubposet
///

-- facePoset
doc ///
    Key
        facePoset
        (facePoset,SimplicialComplex)
    Headline
        generates the face poset of a simplicial complex
    Usage
        F = facePoset D
    Inputs
        D:SimplicialComplex
    Outputs
        F:Poset
    Description
        Text
            The face poset of a @TO "SimplicialComplex"@ is the poset
            of faces with partial ordering given by inclusion.
        Example
            R = QQ[a..d];
            facePoset simplicialComplex {a*b*c, c*d}
    SeeAlso
        faces
///

-- intersectionLattice
doc ///
    Key
        intersectionLattice
        (intersectionLattice,List,Ring)
    Headline
        generates the intersection lattice of a hyperplane arrangement
    Usage
        P = intersectionLattice(L, R)
    Inputs
        L:List
            which gives the equations defining the hyperplane arrangement
        R:Ring
            which the hyperplanes are defined over
    Outputs
        P:Poset
    Description
        Text
            The intersection lattice of a hyperplane arrangement is the 
            lattice of intersections in the arrangement partially ordered
            by containment.
        Example
            R = QQ[x,y,z];
            intersectionLattice({x+y, x+z, y+z}, R)
    SeeAlso
        projectivizeArrangement 
///

-- lcmLattice
doc ///
    Key
        lcmLattice
        (lcmLattice,Ideal)
        (lcmLattice,MonomialIdeal)
        [lcmLattice,Strategy]
    Headline
        generates the lattice of lcms in an ideal
    Usage
        P = lcmLattice I
        P = lcmLattice(I, Strategy => 0)
    Inputs
        I:MonomialIdeal
        I:Ideal
        Strategy=>ZZ
            which is either $0$ or $1$
    Outputs
        P:Poset
    Description
        Text
            The LCM lattice of a @TO "MonomialIdeal"@ is the set of all
            LCMs of subsets of the generators of the ideal with partial
            ordering given by divisbility.  These are particularly useful
            in the study of resolutions of monomial ideals.
        Example
            R = QQ[x,y];
            lcmLattice monomialIdeal(x^2, x*y, y^2)
        Text
            If a non-monomial ideal is passed in, then the @TO "monomialIdeal"@
            of the ideal is used instead.
        Example
           S = QQ[a,b,c,d];
           lcmLattice ideal (b^2-a*d, a*d-b*c, c^2-b*d)
    SeeAlso
        lcm
        monomialIdeal
///

-- partitionLattice
doc ///
    Key
        partitionLattice
        (partitionLattice,ZZ)
    Headline
        computes the lattice of set-partitions of size $n$
    Usage
        P = partitionLattice n
    Inputs
        n:ZZ
            the size of the set to partition
    Outputs
        P:Poset
    Description
        Text
            The partition lattice of order $n$ is the lattice
            of @TO "setPartition"@s of the set $\{1,\ldots,n\}$
            with ordering given by refinement.  That is, the
            set-partition $p$ is greater than or equal to the 
            set-partition $q$ if each part of $p$ is contained in
            exactly one part of $q$.
        Example
            partitionLattice 3
    SeeAlso
        setPartition
///

-- setPartition
doc ///
    Key
        setPartition
        (setPartition,List)
        (setPartition,ZZ)
    Headline
        computes the list of set-partitions of size $n$
    Usage
        L = setPartition n
        L = setPartition S
    Inputs
        S:List
            to be partitioned
        n:ZZ
            the size of the set to partition
    Outputs
        L:List
    Description
        Text
            A set-partition of a @TO "List"@ is a partitioning
            of the list into a finite number of non-empty
            disjoint pieces whose union is the original list.
        Example
            setPartition {2,3,5}
        Text
            The set-partitions of $n$ is the collection of set-partitions
            of the set $\{1,\ldots,n\}$.
        Example
            setPartition 4
    SeeAlso
        partitionLattice
///

-- projectivizeArrangement
doc ///
    Key
        projectivizeArrangement
        (projectivizeArrangement,List,Ring)
    Headline
        computes the intersection poset of a projectivized hyperplane arrangement
    Usage
        P = projectivizeArrangement(L, R)
    Inputs
        L:List
            which gives the equations defining the (possibly non-projective) hyperplane arrangement
        R:Ring
            which the hyperplanes are defined over
    Outputs
        P:Poset
    Description
        Text
            This method returns the @TO "intersectionLattice"@ of the projectivization
            of the specified hyperplane arrangement.
        Example
            R = QQ[x,y,z];
            projectivizeArrangement({x^2-y, y^2-z}, R)
    Caveat
        The variable used for homogenization is $Z$, and so the ring $R$ should not already have this
        variable in use.
    SeeAlso
        intersectionLattice
///

-- randomPoset
doc ///
    Key
        randomPoset
        (randomPoset,List)
        (randomPoset,ZZ)
        [randomPoset,Bias]
        Bias
    Headline
        generates a random poset with a given relation probability
    Usage
        P = randomPoset n
        P = randomPoset G
        P = randomPoset(n, Bias => RR)
        P = randomPoset(G, Bias => RR)
    Inputs
        n:ZZ
            the number of vertices in the poset
        G:List
            the ground set of the poset
        Bias=>RR
            the probability that a given relation will be present
    Outputs
        P:Poset
    Description
        Text
            This method generates a random poset with a given ground
            set ($\{1, \ldots, n\}$, if $n$ is specified).  
        Example
            randomPoset 10
        Text
            The option Bias determines the probability that a given
            relation will be present.  A higher Bias will lead to more
            relations.
        Example
            randomPoset(10, Bias => 0.1)
            randomPoset(10, Bias => 0.9)
    SeeAlso
        random
///

-- standardMonomialPoset
doc ///
    Key
        standardMonomialPoset
        (standardMonomialPoset,MonomialIdeal)
        (standardMonomialPoset,MonomialIdeal,ZZ,ZZ)
    Headline
        generates the poset of divisibility in the monomial basis of an ideal
    Usage
        P = standardMonomialPoset I
        P = standardMonomialPoset(I, minDeg, maxDeg)
    Inputs
        I:MonomialIdeal
        minDeg:ZZ
            the minimum degree of a monomial in the poset
        maxDeg:ZZ
            the maximum degree of a monomial in the poset
    Outputs
        P:Poset
    Description
        Text
            The standard monomial poset of a @TO "MonomialIdeal"@ is the poset
            of monomials in the @TO "quotient"@ with partial ordering given by
            divisibility.
        Example
            R = QQ[x,y,z];
            standardMonomialPoset monomialIdeal(x^2, y^2, z^2, x*y*z)
        Text
            If the integers minDeg and maxDeg are specified, then only the monomials
            with degrees between minDeg and maxDeg are used.  As the standard monomial
            poset is ranked, this is the same as taking all the ranks between minDeg
            and maxDeg.
        Example
            standardMonomialPoset(monomialIdeal(x^4, y^4, z^4, x*y*z), 3, 4)
    SeeAlso
        basis
        monomialIdeal
///

-- youngSubposet
doc ///
    Key
        youngSubposet 
        (youngSubposet,List,List)
        (youngSubposet,List)
        (youngSubposet,ZZ)
    Headline
        generates a subposet of Young's lattice
    Usage
        P = youngSubposet(lo, hi)
        P = youngSubposet hi
        P = youngSubposet n
    Inputs
        lo:List
            which represents a partition
        hi:List
            which represents a partition
        n:ZZ
            the maximum size of a partition
    Outputs
        P:Poset
    Description
        Text
            Young's lattice is the infinite lattice of all @TO "partitions"@
            with partial ordering given by componentwise linear ordering.
        
            If $n$ is specified, then the poset returned is the subposet
            of Young's lattice given by the induced @TO "subposet"@ of
            all partitions of size at most $n$.
        Example
            youngSubposet 4
        Text
            If an upper partition, hi, is specified, then the returned
            poset is the @TO "closedInterval"@ of the Young's lattice
            between lo and hi, where lo either is the empty partition
            or is specified.
        Example
            youngSubposet({3,1}, {4,2,1})
    SeeAlso
        partitions
///

------------------------------------------
-- TeX & GAP
------------------------------------------

-- displayPoset
doc ///
    Key
        displayPoset
        (displayPoset,Poset)
        [displayPoset,SuppressLabels]
        [displayPoset,PDFViewer]
        [displayPoset,Jitter]
        PDFViewer
    Headline
        generates a PDF representation of a poset and attempts to display it
    Usage
        displayPoset P
        displayPoset(P, SuppressLabels => Boolean)
        displayPoset(P, PDFViewer => String)
        displayPoset(P, Jitter => Boolean)
    Inputs
        P:Poset
        SuppressLabels=>Boolean
            whether to display or suppress the labels of the poset
        PDFViewer=>String
            which gives the calling path of a PDF-viewer
        Jitter=>Boolean
            whether to randomly jitter the poset vertices
    Outputs
        n:Nothing
    Description
        Text
            This method generates a PDF of the Poset view LaTeX code which
            uses TikZ.  The method attempts to display the PDF via the 
            specified PDFViewer.  See @TO "texPoset"@ for more about the
            representation.

            Note that @TT "PDFViewer"@ option's default value can be set in
            the "~/.Macaulay2/init-Posets.m2" file.
    SeeAlso
        outputTexPoset
        texPoset
        Jitter
        SuppressLabels
///

-- gapPosetConversion
doc ///
    Key 
        gapPosetConversion
        (gapPosetConversion,Array)
        (gapPosetConversion,Poset)
        (gapPosetConversion,String)
    Headline
        converts between Macaulay2's Posets and GAP's Posets
    Usage
        P = gapPosetConversion A
        P = gapPosetConversion S
        S = gapPosetConversion P
    Inputs
        A:Array
            representing a poset in GAP-format
        S:String
            representing a poste in GAP-format
        P:Poset
    Outputs
        S:String
            representing a poste in GAP-format
        P:Poset
    Description
        Text
            The GAP package @TT "Simplicial Homology"@, available at 
            @HREF "http://www.eecis.udel.edu/~dumas/Homology/"@, provides methods for 
            using posets within GAP.  According to the documentation, posets are
            stored in GAP in the following manor:  The ground set is the set of integers
            $1..n+1$ and the relations are stored in a list of length $n$, where the $i$th
            entry is the set of vertices which cover $i$ in the poset.  In particular, $1$
            should be the unique minimal element and $n+1$ should be the unique maximal
            element. 

            When converting from GAP format, the conversion is direct using the above convention.
            In this example, @TT "S"@ is generated with the GAP command 
            @TT "OrderRelationToPoset(Subsets([1,2,3]), IsSubset);"@.
        Example
            S = "[ [ 3 ], [ 10 ], [ 4, 7, 9 ], [ 5, 6 ], [ 2 ], [ 2 ], [ 5, 8 ], [ 2 ], [ 6, 8 ], [  ] ]";
            P = gapPosetConversion S
            P == augmentPoset booleanLattice 3
        Text
            When convering to GAP format, the method automatically augments the poset.  In this example,
            the $3$ chain becomes a $5$ chain in GAP format.
        Example
            gapPosetConversion chain 3
   SeeAlso
        poset
///

-- outputTexPoset
doc ///
    Key
        outputTexPoset
        (outputTexPoset,Poset,String)
        [outputTexPoset,SuppressLabels]
        [outputTexPoset,Jitter]
    Headline
        writes a LaTeX file with a TikZ-representation of a poset
    Usage
        outputTexPoset(P, f)
        outputTexPoset(P, f, SuppressLabels => Boolean)
        outputTexPoset(P, f, Jitter => Boolean)
    Inputs
        P:Poset
        f:String
            the name of the file to be created
        SuppressLabels=>Boolean
            whether to display or suppress the labels of the poset
        Jitter=>Boolean
            whether to randomly jitter the poset vertices
    Outputs
        n:Nothing
    Description
        Text
            This method writes a TikZ-representation of the given poset to the
            specified file.  See @TO "texPoset"@ for more about the representation.
    SeeAlso
        displayPoset
        texPoset
        Jitter
        SuppressLabels
///

-- texPoset
doc ///
    Key
        texPoset
        (texPoset,Poset)
        [texPoset,SuppressLabels]
        [texPoset,Jitter]
        Jitter
        SuppressLabels
        (tex, Poset)
    Headline
        generates a string containing a TikZ-figure of a poset
    Usage
        texPoset P
        texPoset(P, SuppressLabels => Boolean)
        texPoset(P, Jitter => Boolean)
        tex P
    Inputs
        P:Poset
        SuppressLabels=>Boolean
            whether to display or suppress the labels of the poset
        Jitter=>Boolean
            whether to randomly jitter the poset vertices
    Outputs
        S:String
            a TikZ-figure of $P$
    Description
        Text
            This method creates a TikZ-figure of the given poset which
            can be included in a LaTeX file.  The representation places
            the vertices on horizontal lines corresponding to the 
            @TO "filtration"@ of the poset.  The only displayed edges are
            the @TO "coveringRelations"@ which are oriented so that lower
            vertices less than higher vertices.

            The method attempts to display labels in a sane way, if they
            are not suppressed by the @TT "SuppressLabels"@ option.  
            Note that the @TT "SuppressLabels"@ option's default value can
            be set in the "~/.Macaulay2/init-Posets.m2" file.

            Further, sometimes the vertices of the poset line up in unfortunate
            ways that causes edges to touch other vertices.  Using the 
            @TT "Jitter"@ option can relieve this by adding a small random
            horizontal shift to each vertex.
        Example
            texPoset booleanLattice 2
            texPoset(booleanLattice 2, Jitter => true)

    Caveat
        Calling texPoset via the command @TO "tex"@ expects that no options are given.
    SeeAlso
        coveringRelations
        displayPoset
        filtration
        outputTexPoset
///

------------------------------------------
-- Vertices & vertex properties
------------------------------------------

-- atoms
doc ///
    Key
        atoms
        (atoms,Poset)
    Headline
        computes the list of elements covering the minimal elements of a poset
    Usage
        A = atoms P
    Inputs
        P:Poset
    Outputs
        A:List
            elements covering the minimal elements of a poset
    Description
        Text
            An atom of a poset is an element which covers a minimal element
            of the poset.
        Example
            atoms booleanLattice 3
            atoms chain 5
    SeeAlso
        coveringRelations
        minimalElements
///

-- compare
doc ///
    Key
        compare
        (compare,Poset,Thing,Thing)
    Headline
        compares two elements in a poset
    Usage
        r = compare(P, a, b)
    Inputs
        P:Poset
        a:Thing
            an element of the poset
        b:Thing
            an element of the poset
    Outputs
        r:Boolean
            whether $a \leq b$ in $P$
    Description
        Text
            This method determines if two elements are comparable and further
            if $a$ is less than or equal to $b$ in $P$.
        Example
            P = poset {{a,b},{a,c}};
            compare(P, a, b)
            compare(P, c, a)
        Text
            If two elements are incomparable, then the result is false.
        Example
            compare(P, b, c)
///

-- connectedComponents
doc ///
    Key
        connectedComponents
        (connectedComponents,Poset)
    Headline
        generates a list of connected components of a poset
    Usage
        C = connectedComponents P
    Inputs
        P:Poset
    Outputs
        C:List
            containing lists of vertices, each of which is a connected component of $P$   
    Description
        Text
            A connected component of $P$ is a set of vertices of $P$ such that every
            between every pair of vertices $u$ and $v$ in the set there exists a chain 
            of vertices $(a_0=u,a_1,\ldots,a_n=v)$ such that $a_{i-1}$ and $a_i$ are 
            comparable in $P$ for each $i$.
        Example
            C = chain 3;
            connectedComponents C
            S = sum(5, i -> naturalLabeling(C, 10*i));
            connectedComponents S
        Text
            This method was ported from John Stembridge's Maple package available at
            @HREF "http://www.math.lsa.umich.edu/~jrs/maple.html#posets"@.  
///

-- filtration
doc ///
    Key
        filtration
        (filtration,Poset)
    Headline
        generates the filtration of a posett
    Usage
        F = filtration P
    Inputs
        P:Poset
    Outputs
        F:List
            the filtration of $P$
    Description
        Text
            The filtration of $P$ is a partitioning $F$ of the vertices such that 
            $F_0$ is the set of minimal elements of $P$, $F_1$ is the set of minimal
            elements of $P - F_0$, and so forth.  
        Example
            P = poset {{a,b}, {b,c}, {c,d}, {a,e}, {e,d}};
            filtration P
        Text
            The filtration of a ranked poset is the same as the ranking of the poset.
        Example
            B = booleanLattice 3;
            F = filtration B
            R = rankPoset B
            sort \ F === sort \ R
        Text
            The @TO "flatten"@ of the filtration is a linear extension of the poset.
        Example
            member(flatten F, linearExtensions B)
        Text
            This method was ported from John Stembridge's Maple package available at
            @HREF "http://www.math.lsa.umich.edu/~jrs/maple.html#posets"@.  
    SeeAlso
        linearExtensions
        minimalElements
        rankPoset
///

-- joinExists
doc ///
    Key
        joinExists
        (joinExists,Poset,Thing,Thing)
    Headline
        determines if the join exists for two elements of a poset
    Usage
        j = joinExists(P, a, b)
    Inputs
        P:Poset
        a:Thing
            an element of the poset
        b:Thing
            an element of the poset
    Outputs
        j:Boolean
            whether the join exists for $a$ and $b$ in $P$
    Description
        Text
            The join of $a$ and $b$ in $P$, if it exists, is the unique
            least element greater than both $a$ and $b$.
        Example
            P = poset {{a,b}, {a,c}, {a,d}, {c,e}, {d,e}};
            joinExists(P, b, c)
            joinExists(P, c, d)
            Q = poset {{a,b}, {a,c}, {b,d}, {c,d}, {b,e}, {c,e}};
            joinExists(P, b, c)
    SeeAlso
        meetExists
        posetJoin
        posetMeet
///

-- joinIrreducibles
doc ///
    Key
        joinIrreducibles
        (joinIrreducibles,Poset)
    Headline
        determines the join irreducible elements of a poset
    Usage
        J = joinIrreducibles P
    Inputs
        P:Poset
    Outputs
        J:List
    Description
        Text
            An element $a$ of $P$ is join irreducible if it is not the join
            of any set of elements not containing $a$.
        Example
            joinIrreducibles booleanLattice 3
    SeeAlso
        joinExists
        meetIrreducibles
        posetJoin
///

-- maximalElements
doc ///
    Key
        maximalElements
        (maximalElements,Poset)
    Headline
        determines the maximal elements of a poset
    Usage
        M = maximalElements P
    Inputs
        P:Poset
    Outputs
        M:List
    Description
        Text
            An element of $P$ is a maximal element if it no other
            element of $P$ is greater than it.
        Example
            P = poset {{a,b}, {a,c}, {c,d}};
            maximalElements P
    SeeAlso
        minimalElements
///

-- meetExists
doc ///
    Key
        meetExists
        (meetExists,Poset,Thing,Thing)
    Headline
        determines if the meet exists for two elements of a poset
    Usage
        m = meetExists(P, a, b)
    Inputs
        P:Poset
        a:Thing
            an element of the poset
        b:Thing
            an element of the poset
    Outputs
        m:Boolean
            whether the meet exists for $a$ and $b$ in $P$
    Description
        Text
            The meet of $a$ and $b$ in $P$, if it exists, is the
            unique greatest element less than both $a$ and $b$.
        Example
            P = poset {{a,b}, {a,c}, {b,d}, {c,d}, {e,d}};
            meetExists(P, b, c)
            meetExists(P, b, e)
            Q = poset {{a,b}, {a,c}, {d,b}, {d,c}, {b,e}, {c,e}};
            meetExists(Q, b, c)
    SeeAlso
        joinExists
        posetJoin
        posetMeet
///

-- meetIrreducibles
doc ///
    Key
        meetIrreducibles
        (meetIrreducibles,Poset)
    Headline
        determines the meet irreducible elements of a poset
    Usage
        M = meetIrreducibles P
    Inputs
        P:Poset
    Outputs
        M:List
    Description
        Text
            An element $a$ of $P$ is meet irreducible if it is not the meet
            of any set of elements not containing $a$.
        Example
            meetIrreducibles booleanLattice 3
    SeeAlso
        joinIrreducibles
        meetExists
        posetMeet
///

-- minimalElements
doc ///
    Key
        minimalElements
        (minimalElements,Poset)
    Headline
        determines the minimal elements of a poset
    Usage
        M = minimalElements P
    Inputs
        P:Poset
    Outputs
        M:List
    Description
        Text
            An element of $P$ is a minimal element if it no other
            element of $P$ is less than it.
        Example
            P = poset {{a,b}, {b,c}, {d,c}};
            minimalElements P
    SeeAlso
        maximalElements
///

-- posetJoin
doc ///
    Key
        posetJoin
        (posetJoin,Poset,Thing,Thing)
    Headline
        determines the join for two elements of a poset
    Usage
        j = posetJoin(P, a, b)
    Inputs
        P:Poset
        a:Thing
            an element of the poset
        b:Thing
            an element of the poset
    Outputs
        j:Thing
            the least element greater than both $a$ and $b$, if it exists
    Description
        Text
            The join of $a$ and $b$ in $P$, if it exists, is the unique
            least element greater than both $a$ and $b$.
        Example
            B = booleanLattice 3;
            posetJoin(B, "001", "100")
    SeeAlso
        joinExists
        posetMeet
///

-- posetMeet
doc ///
    Key
        posetMeet
        (posetMeet,Poset,Thing,Thing)
    Headline
        determines the meet for two elements of a poset
    Usage
        m = posetMeet(P, a, b)
    Inputs
        P:Poset
        a:Thing
            an element of the poset
        b:Thing
            an element of the poset
    Outputs
        m:Thing
            the greatest element less than both $a$ and $b$, if it exists
    Description
        Text
            The meet of $a$ and $b$ in $P$, if it exists, is the
            unique greatest element less than both $a$ and $b$.
        Example
            B = booleanLattice 3;
            posetMeet(B, "011", "110")
    SeeAlso
        meetExists
        posetJoin
///

-- rankFunction
doc ///
    Key
        rankFunction
        (rankFunction,Poset)
    Headline
        computes the rank function of a ranked poset
    Usage
        rk = rankFunction P
    Inputs
        P:Poset
    Outputs
        rk:List
            such that entry $i$ is the rank of the $i$th member of the ground set
    Description
        Text
            The poset $P$ is ranked if there exists an integer function $r$ on
            the vertex set of $P$ such that for each $a$ and $b$ in the poset
            if $b$ covers $a$ then $r(b) - r(a) = 1$.  

            This method returns one such ranking function.
        Example
            rankFunction chain 5
            rankFunction booleanLattice 3
        Text
            This method was ported from John Stembridge's Maple package available at
            @HREF "http://www.math.lsa.umich.edu/~jrs/maple.html#posets"@.  
    SeeAlso
        isRanked
        rankPoset
///

-- rankPoset
doc ///
    Key
        rankPoset
        (rankPoset,Poset)
    Headline
        generates a list of lists representing the ranks of a ranked poset
    Usage
        L = rankPoset P
    Inputs
        P:Poset
    Outputs
        L:List
            containing lists such that the $i$th list is the set of 
            vertices in the $i$th rank of $P$
    Description
        Text
            The poset $P$ is ranked if there exists an integer function $r$ on
            the vertex set of $P$ such that for each $a$ and $b$ in the poset
            if $b$ covers $a$ then $r(b) - r(a) = 1$.  

            This method returns the list of vertices in each rank.
        Example
            rankPoset chain 5
            rankPoset booleanLattice 3
        Text
            This method uses the method @TO "rankFunction"@, which was ported
            from John Stembridge's Maple package available at
            @HREF "http://www.math.lsa.umich.edu/~jrs/maple.html#posets"@.  
    SeeAlso
        isRanked
        rankFunction
///

------------------------------------------
-- Relations & relation properties
------------------------------------------

-- allRelations
doc ///
    Key
        allRelations
        (allRelations,Poset)
        (allRelations,Poset,Boolean)
    Headline
        computes all relations of a poset
    Usage
        R = allRelations P
        R = allRelations(P, NoLoops)
    Inputs
        P:Poset
        NoLoops:Boolean
            whether loops, i.e., relations of the form $\{a,a\}$, should be returned
    Outputs
        R:List
            containing all relations between elements of $P$
    Description
        Text
            This method returns all relations of a poset, though loops may
            be suppressed with the input @TT "NoLoops"@.
        Example
            P = divisorPoset 12;
            allRelations P
            allRelations(P, true)
    SeeAlso
        compare
        coveringRelations
///

-- antichains
doc ///
    Key
        antichains
        (antichains,Poset)
        (antichains,Poset,ZZ)
    Headline
        computes all antichains of a poset
    Usage
        L = antichains P
    Inputs
        P:Poset
        k:ZZ
            select on antichains of a given length
    Outputs
        L:List
            containing all antichains of $P$
    Description
        Text
            A set of elements of $P$ is called an antichain if no
            two distinct elements of the set are comparable.
        Example
            D = divisorPoset 12;
            antichains D
        Text
            With the input @TT "k"@, the method restricts to 
            only antichains of that length.  In a @TO "divisorPoset"@, all
            chains of length $2$ describe exactly the non-divisor-multiple
            pairs.
        Example
            antichains(D, 2)
        Text
            Since every distinct pair of vertices in a @TO "chain"@
            is comparable, the only antichains of a chain are the
            singleton sets and the empty set.
        Example
            antichains chain 5
    SeeAlso
        chains
        isAntichain
///

-- chains
doc ///
    Key
        chains
        (chains,Poset)
        (chains,Poset,ZZ)
    Headline
        computes all chains of a poset
    Usage
        L = chains P
        L = chains(P, k)
    Inputs
        P:Poset
        k:ZZ
            select on chains of a given length
    Outputs
        L:List
            containing all chains of $P$
    Description
        Text
            A set of elements of $P$ is called a chain if every
            pair of elements in the set are comparable.
        Example
            D = divisorPoset 12;
            chains D
        Text
            With the input @TT "k"@, the method restricts to 
            only chains of that length.  In a @TO "divisorPoset"@, all
            chains of length $2$ describe exactly the divisor-multiple
            pairs.
        Example
            chains(D, 2)
    SeeAlso
        antichains
///

-- coveringRelations
doc ///
    Key
        coveringRelations
        (coveringRelations,Poset)
    Headline
        computes the minimal list of generating relations of a poset
    Usage
        R = coveringRelations P
    Inputs
        P:Poset
    Outputs
        R:List
            the minimal list of generating relations of $P$
    Description
        Text
            A relation $a < b$ of elements in $P$ is a covering relation
            if there exists no $c$ in $P$ such that $a < c < b$.  The set
            of covering relations is the minimal list of relations in $P$
            that describes all relations of $P$.
        Example
            coveringRelations divisorPoset 12
    SeeAlso
        allRelations
///

-- flagChains
doc ///
    Key
        flagChains
        (flagChains,Poset,List)
    Headline
        computes the maximal chains in a list of flags of a ranked poset
    Usage
        C = flagChains(P, L)
    Inputs
        P:Poset
        L:List
            containing rank indices
    Outputs
        C:List
            all maximal chains of $P$ containing only elements in the flags indexed by $L$
    Description
        Text
            The flag chains of $P$ with respect to $L$ are exactly the @TO "maximalChains"@
            of the @TO "flagPoset"@ of $P$ with respect to $L$.
        Example
            D = divisorPoset(2^2*3*5);
            rankFunction D
            flagChains(D, {1,2,3})
    SeeAlso
        flagPoset
        isRanked
        maximalChains
        rankPoset
///

-- isAntichain
doc ///
    Key
        isAntichain
        (isAntichain,Poset,List)
    Headline
        determines if a given list of vertices is an antichain of a poset
    Usage
        i = isAntichain(P, L)
    Inputs
        P:Poset
        L:List
            containing elements of $P$
    Outputs
        i:Boolean
            whether $L$ is an antichain of $P$
    Description
        Text
            A set of elements of $P$ is called an antichain if no
            two distinct elements of the set are comparable.
        Example
            D = divisorPoset 12;
            isAntichain(D, {2,3})
            isAntichain(D, {2,6})
    SeeAlso
        antichains
///

-- linearExtensions
doc ///
    Key
        linearExtensions
        (linearExtensions,Poset)
    Headline
        computes all linear extensions of a poset
    Usage
        L = linearExtensions P
    Inputs
        P:Poset
    Outputs
        L:List
            all possible linear extensions of $P$
    Description
        Text
            A linear extension of the partial order on $P$ is a total order 
            on the elements of $P$ that is compatible with the partial order.
        Example
            P = divisorPoset 12;
            L = linearExtensions P
        Text
            The @TO "flatten"@ of the @TO "filtration"@ of $P$ is always a 
            linear extension.  This approach is much faster, especially for
            posets with many linear extensions.
        Example
            F = flatten filtration P
            member(F, L)
        Text
            The partial order of a @TO "chain"@ is the total order of the elements.
        Example
            linearExtensions chain 10
        Text
            This method was ported from John Stembridge's Maple package available at
            @HREF "http://www.math.lsa.umich.edu/~jrs/maple.html#posets"@.  
    SeeAlso
        filtration
///

-- maximalAntichains
doc ///
    Key
        maximalAntichains
        (maximalAntichains,Poset)
    Headline
        computes all maximal antichains of a poset
    Usage
        M = maximalAntichains P
    Inputs
        P:Poset
    Outputs
        M:List
            all maximal antichains of $P$
    Description
        Text
            A set of elements of $P$ is called an antichain if no
            two distinct elements of the set are comparable.  An
            antichain is maximal if it is not properly contained
            in any other antichain of $P$.
        Example
            maximalAntichains divisorPoset 30
    SeeAlso
        antichains
        maximalChains
///

-- maximalChains
doc ///
    Key
        maximalChains
        (maximalChains,Poset)
    Headline
        computes all maximal chains of a poset
    Usage
        M = maximalChains P
    Inputs
        P:Poset
    Outputs
        M:List
            all maximal chains of $P$
    Description
        Text
            A set of elements of $P$ is called a chain if every
            pair of elements of the set are comparable.  A
            chain is maximal if it is not properly contained
            in any other chain of $P$.
        Example
            maximalChains divisorPoset 30
    SeeAlso
        chains
        maximalAntichains
///

------------------------------------------
-- Enumerative invariants
------------------------------------------

-- characteristicPolynomial
doc ///
    Key
        characteristicPolynomial
        (characteristicPolynomial,Poset)
        [characteristicPolynomial,VariableName]
    Headline
        computes the characteristic polynomial of a ranked poset
    Usage
        p = characteristicPolynomial P
        p = characteristicPolynomial(P, VariableName => symbol)
    Inputs
        P:Poset
            a ranked poset
        VariableName=>Symbol
    Outputs
        p:RingElement
            the characteristic polynomial of $P$
    Description
        Text
            The characteristic polynomial of a ranked poset is the generating
            function with variable $q$ such that the coefficient of $q^r$ is
            the sum overall vertices of rank $r$ of the Moebius function of $v$.
        
            The characteristic polynomial of the @TO "chain"@ of $n$ is $q^{n-1}(q-1)$.
        Example
            n = 5;
            factor characteristicPolynomial chain n
        Text
            And the characteristic polynomial of the @TO "booleanLattice"@ of 
            $n$ is $(q-1)^n$.
        Example
            factor characteristicPolynomial booleanLattice n
    SeeAlso
        isRanked
        moebiusFunction
///

-- flagfPolynomial
doc ///
    Key
        flagfPolynomial
        (flagfPolynomial,Poset)
        [flagfPolynomial,VariableName]
    Headline
        computes the flag-f polynomial of a ranked poset
    Usage
        ff = flagfPolynomial P
        ff = flagfPolynomial(P, VariableName => symbol)
    Inputs
        P:Poset
            a ranked poset
        VariableName=>Symbol
    Outputs
        ff:RingElement
            the flag-f polynomial of $P$
    Description
        Text
            Suppose $P$ is a rank $r$ poset.  For each strictly increasing sequence
            $(i_1, \ldots, i_k)$ with $0 \leq i_j \leq i_k$, the coefficient of
            $q_i_1 \cdots q_i_k$ is the number of @TO "flagChains"@ in the ranks
            $i_1, \cdots, i_k$.

            The flag-f polynomial of the $n$ @TO "chain"@ is $(q_0 + 1)\cdots(q_{n-1}+1)$.
        Example
            n = 4;
            factor flagfPolynomial chain n
    SeeAlso
        flagChains
        flaghPolynomial
        isRanked
///

-- flaghPolynomial
doc ///
    Key
        flaghPolynomial
        (flaghPolynomial,Poset)
        [flaghPolynomial,VariableName]
    Headline
        computes the flag-h polynomial of a ranked poset
    Usage
        fh = flaghPolynomial P
        fh = flaghPolynomial(P, VariableName => symbol)
    Inputs
        P:Poset
            a ranked poset
        VariableName=>Symbol
    Outputs
        fh:RingElement
            the flag-h polynomial of $P$
    Description
        Text
            Suppose $f$ is the @TO "flagfPolynomial"@ of $P$.  The flag-h polynomial
            of $P$ is the polynomial $(1-q_0)\cdots(1-q_r)f(q_0/(1-q_0), \ldots, q_r/(1-q_r))$.
        Example
            flaghPolynomial booleanLattice 3
        Text
            The flag-h polynomial of the $n$ @TO "chain"@ is $1$.
        Example
            flaghPolynomial chain 5
    SeeAlso
        flagChains
        flagfPolynomial
        isRanked
///

-- fPolynomial
doc ///
    Key
        fPolynomial
        (fPolynomial,Poset)
        [fPolynomial,VariableName]
    Headline
        computes the f-polynomial of a poset
    Usage
        f = fPolynomial P
        f = fPolynomial(P, VariableName => symbol)
    Inputs
        P:Poset
        VariableName=>Symbol
    Outputs
        f:RingElement
            the f-polynomial of $P$
    Description
        Text
            The f-polynomial of $P$ is the polynomial such that the 
            coefficient on $q^i$ is the number of @TO "chains"@ of
            length $i$ in $P$.

            The f-polynomial of the $n$ @TO "chain"@ is $(q+1)^n$.
        Example
            n = 5;
            factor fPolynomial chain n
    SeeAlso
        chains
        hPolynomial
///

-- greeneKleitmanPartition
doc ///
    Key
        greeneKleitmanPartition
        (greeneKleitmanPartition,Poset)
        [greeneKleitmanPartition,Strategy]
    Headline
        computes the Greene-Kleitman partition of a poset
    Usage
        l = greeneKleitmanPartition P
        l = greeneKleitmanPartition(P, Strategy => "chains")
        l = greeneKleitmanPartition(P, Strategy => "antichains")
    Inputs
        P:Poset
        Strategy=>String
            either "chains" or "antichains"
    Outputs
        l:Partition
            the Greene-Kleitman partition of $P$
    Description
        Text
            The Greene-Kleitman partition $l$ of $P$ is the partition
            such that the sum of the first $k$ parts of $l$ is the maximal
            number of elements in a union of $k$ @TO "chains"@ in $P$.
        Example
            P = poset {{1,2},{2,3},{3,4},{2,5},{6,3}};
            greeneKleitmanPartition P
        Text
            The conjugate of $l$ has the same property, but with chains
            replaced by @TO "antichains"@.  Because of this, it is often
            better to count via antichains instead of chains.  This can
            be done by passing "antichains" as the Strategy.
        Example 
            D = dominanceLattice 6;
            time greeneKleitmanPartition(D, Strategy => "antichains")
            time greeneKleitmanPartition(D, Strategy => "chains")
        Text
            The Greene-Kleitman partition of the $n$ @TO "chain"@ is the
            partition of $n$ with $1$ part.
        Example
            greeneKleitmanPartition chain 10
    SeeAlso
        chains
        antichains
///

-- hPolynomial
doc ///
    Key
        hPolynomial
        (hPolynomial,Poset)
        [hPolynomial,VariableName]
    Headline
        computes the h-polynomial of a poset
    Usage
        h = hPolynomial P
        h = hPolynomial(P, VariableName => symbol)
    Inputs
        P:Poset
        VariableName=>Symbol
    Outputs
        h:RingElement
            the h-polynomial of $P$
    Description
        Text
            Suppose $f$ is the @TO "fPolynomial"@ of $P$, and $d$ is the degree 
            of $f$.  Then the h-polynomial of $P$ is the polynomial 
            $(1-q)^d f(q/(1-q))$.
        Example
            hPolynomial booleanLattice 3
        Text
            The h-polynomial of the $n$ @TO "chain"@ is $1$.
        Example
            hPolynomial chain 5
    SeeAlso
        chains
        fPolynomial
///

-- moebiusFunction
doc ///
    Key
        moebiusFunction
        (moebiusFunction,Poset)
    Headline
        computes the Moebius function at every pair of elements of a poset
    Usage
        mu = moebiusFunction P
    Inputs
        P:Poset
    Outputs
        mu:HashTable
            the Moebius function of $P$
    Description
        Text
            The Moebius function of $P$ is a function defined at pairs of
            vertices of $P$ with the properties:
            $mu(a,a) = 1$ for all $a$ in $P$, and $mu(a,b) = -sum(mu(a,c))$
            over all $a \leq c < b$. 

            The Moebius function of the $n$ @TO "chain"@ is $1$ at $(a,a)$ 
            for all $a$, $-1$ at $(a, a+1)$ for $1 \leq a < n$, and $0$ 
            every where else.
        Example
            moebiusFunction chain 3
///

-- rankGeneratingFunction
doc ///
    Key
        rankGeneratingFunction
        (rankGeneratingFunction,Poset)
        [rankGeneratingFunction,VariableName]
    Headline
        computes the rank generating function of a ranked poset
    Usage
        r = rankGeneratingFunction P
        r = rankGeneratingFunction(P, VariableName => symbol)
    Inputs
        P:Poset
            a ranked poset
        VariableName=>Symbol
    Outputs
        r:RingElement
            the rank generating function of $P$
    Description
        Text
            The rank generating function of $P$ is the polynomial
            with the coefficient of $q^i$ given by the number of
            vertices in rank $i$ of $P$.

            The rank generating function of the $n$ @TO "chain"@ is 
            $q^{n-1} + \cdots + q + 1$.
        Example
            n = 5;
            rankGeneratingFunction chain n
        Text
            The rank generating function of the $n$ @TO "booleanLattice"@
            is $(q+1)^n$.
        Example
            factor rankGeneratingFunction booleanLattice n
    SeeAlso
        isRanked
        rankPoset
///

-- zetaPolynomial
doc ///
    Key
        zetaPolynomial
        (zetaPolynomial,Poset)
        [zetaPolynomial,VariableName]
    Headline
        computes the zeta polynomial of a poset
    Usage
        z = zetaPolynomial P
        z = zetaPolynomial(P, VariableName => symbol)
    Inputs
        P:Poset
        VariableName=>Symbol
    Outputs
        z:RingElement
            the zeta polynomial of $P$
    Description
        Text
            The zeta polynomial of $P$ is the polynomial
            $z$ such that for every $i > 1$, $z(i)$ is the number
            of weakly increasing chains of $i-1$ vertices in $P$.

            The zeta polynomial of the $n$ @TO "booleanLattice"@ is
            $q^n$.
        Example
            B = booleanLattice 3;
            z = zetaPolynomial B
        Text
            Thus, $z(2)$ is the number of vertices of $P$,
            and $z(3)$ is the number of total relations in $P$.
        Example
            #B.GroundSet == sub(z, (ring z)_0 => 2)
            #allRelations B == sub(z, (ring z)_0 => 3)
    SeeAlso
        chains
///

------------------------------------------
-- Properties
------------------------------------------

-- dilworthNumber
doc ///
    Key
        dilworthNumber
        (dilworthNumber,Poset)
    Headline
        computes the Dilworth number of a poset
    Usage
        d = dilworthNumber P
    Inputs
        P:Poset
    Outputs
        d:ZZ
            the maximal length of an antichain
    Description
        Text
            The Dilworth number of a poset is the maximal length of an antichain.

            The Dilworth number of a @TO "chain"@ is always 1.
        Example
            n = 5;
            dilworthNumber chain n
        Text
            The Dilworth number of the $n$ @TO "booleanLattice"@ is $n*(n-1)/2$.
        Example
            dilworthNumber booleanLattice n
            n*(n-1)//2
    SeeAlso
        antichains
        dilworthLattice
        maximalAntichains
///

-- height
doc ///
    Key
        (height,Poset)
    Headline
        computes the height of a poset
    Usage
        h = height P
    Inputs
        P:Poset
    Outputs
        h:ZZ
            the height of $P$
    Description
        Text
            The height of a poset is one less than the length of the longest chain.

            The $n$ @TO "chain"@ has height $n-1$.
        Example
            n = 5;
            height chain n
    SeeAlso
        chains
        maximalChains
///

-- isAtomic
doc ///
    Key 
        isAtomic
        (isAtomic,Poset)
    Headline
        determines if a lattice is atomic
    Usage
        i = isAtomic P
    Inputs
        P:Poset
            a lattice
    Outputs
        i:Boolean
            whether $P$ is atomic
    Description
        Text
            The lattice $P$ is atomic if every non-minimal vertex of $P$ is
            the join of atoms of $P$.  Equivalently, $P$ is atomic if every
            non-minimal, non-atom vertex of $P$ covers at least two vertices.

            The diamond poset is atomic.  Also $n$ @TO "booleanLattice"@s are atomic.
        Example
            P = poset {{1, 2}, {1, 3}, {1, 4}, {2, 5}, {3, 5}, {4, 5}};
            isLattice P
            isAtomic P
            isAtomic booleanLattice 4
        Text
            The following lattice is non-atomic.  Also, $n$ @TO "chain"@s are 
            non-atomic, for $n \geq 3$.
        Example
            Q = poset {{1, 2}, {1, 3}, {2, 4}, {2, 5}, {3, 4}, {4, 6}, {5, 6}};
            isLattice Q
            isAtomic Q
            isAtomic chain 5
    SeeAlso
        atoms
        isLattice
///

-- isBounded
doc ///
    Key
        isBounded
        (isBounded,Poset)
    Headline
        determines if a poset is bounded
    Usage
        i = isBounded P
    Inputs
        P:Poset
    Outputs
        i:Boolean
            whether $P$ is bounded
    Description
        Text
            The poset $P$ is bounded if it has a unique minimal 
            element and a unique maximal element.
        
            The $n$ @TO "chain"@ and $n$ @TO "booleanLattice"@ are bounded.
        Example
            n = 5;
            isBounded chain n
            B = booleanLattice n;
            isBounded B
        Text
            The middle ranks of an $n$ boolean lattice are not bounded.
        Example
            isBounded flagPoset(B, {1,2,3,4})
    SeeAlso
        maximalElements
        minimalElements
///

-- isConnected
doc ///
    Key
        isConnected
        (isConnected,Poset)
    Headline
        determines if a poset is connected
    Usage
        i = isConnected P
    Inputs
        P:Poset
    Outputs
        i:Boolean
            whether $P$ is connected
    Description
        Text
            The poset $P$ is connected if the number of @TO "connectedComponents"@
            is $1$.  Equivalently, the poset $P$ is connected if between every pair
            of vertices in $P$ there exists a chain of relations going from one
            to the other.

            The @TO "divisorPoset"@ of $n$ is always connected.
        Example
            isConnected divisorPoset 18
        Text
            The disjoint union of any two posets on disjoint vertex sets is disconnected.
        Example
            C = chain 3;
            P = sum(5, i -> naturalLabeling(C, 10*i));
            isConnected P
    SeeAlso
        connectedComponents
///

-- isDistributive
doc ///
    Key
        isDistributive
        (isDistributive,Poset)
    Headline
        determines if a lattice is distributive
    Usage
        i = isDistributive P 
    Inputs
        P:Poset
            a lattice
    Outputs
        i:Boolean
            whether $P$ is distributive
    Description
        Text
            The lattice $P$ is distributive if the meet operation distributes
            over the join operation.  Equivalently, $P$ is distributive if the
            join operation distributes over the meet operation.

            The $n$ @TO "booleanLattice"@ is distributive.
        Example
            isDistributive booleanLattice 3
        Text
            The pentagon lattice and diamond lattice are prototypical non-distributive lattices.
        Example
            P = poset {{1,2}, {1,3}, {3,4}, {2,5}, {4, 5}};
            isLattice P
            isDistributive P
            D = poset {{1,2}, {1,3}, {1,4}, {2,5}, {3,5}, {4,5}};
            isLattice D
            isDistributive D
    SeeAlso
        posetJoin
        posetMeet
        isLattice
///

-- isEulerian
doc ///
    Key
        isEulerian
        (isEulerian,Poset)
    Headline
        determines if a ranked poset is Eulerian
    Usage
        i = isEulerian P
    Inputs
        P:Poset
            a ranked poset
    Outputs
        i:Boolean
            whether $P$ is Eulerian
    Description
        Text
            The poset $P$ is Eulerian if every non-trivial @TO "closedInterval"@
            of $P$ has an equal number of vertices of even and odd rank.

            The $n$ @TO "chain"@ is non-Eulerian for $n \geq 3$.
        Example
            isEulerian chain 10
        Text
            The @TO "facePoset"@ of the @TO "simplicialComplex"@ of an $n$ cycle
            is Eulerian.
        Example
            n = 10;
            R = QQ[x_0..x_(n-1)];
            F = facePoset simplicialComplex apply(n, i -> x_i * x_((i+1)%n));
            isEulerian F
    SeeAlso
        closedInterval
        isRanked
        moebiusFunction
///

-- isGeometric
doc ///
    Key
        isGeometric
        (isGeometric,Poset)
    Headline
        determines if a lattice is geometric
    Usage
        i = isGeometric P
    Inputs
        P:Poset
            a lattice
    Outputs
        i:Boolean
            whether $P$ is geometric
    Description
        Text
            The lattice $P$ is geometric if it @TO "isAtomic"@ and @TO "isUpperSemimodular"@.

            The diamond poset is geometric.  Also $n$ @TO "booleanLattice"@s are geometric.
        Example
            P = poset {{1, 2}, {1, 3}, {1, 4}, {2, 5}, {3, 5}, {4, 5}};
            isLattice P
            isGeometric P
            isGeometric booleanLattice 4
        Text
            The following lattice is non-geometric.
        Example
            Q = poset {{1, 2}, {1, 3}, {2, 4}, {2, 5}, {3, 4}, {4, 6}, {5, 6}};
            isLattice Q
            isGeometric
    SeeAlso
        isAtomic
        isLattice
        isUpperSemimodular
///

-- isGraded
doc ///
    Key
        isGraded
        (isGraded,Poset)
    Headline
        determines if a poset is graded
    Usage
        i = isGraded P
    Inputs
        P:Poset
    Outputs
        i:Boolean
            whether the maximal chains of $P$ are the same length
    Description
        Text
            The poset $P$ is graded if all of its @TO "maximalChains"@ are the
            same length.

            Clearly, the $n$ @TO "chain"@ and the $n$ @TO "booleanLattice"@ are
            graded.
        Example
            n = 5;
            isGraded chain n
            isGraded booleanLattice n
        Text
            However, the pentagon lattice is not graded.
        Example
            P = poset {{1,2}, {1,3}, {3,4}, {2,5}, {4, 5}};
            isGraded P
    SeeAlso
        chains
        maximalChains
///

-- isLattice
doc ///
    Key
        isLattice
        (isLattice,Poset)
    Headline
        determines if a poset is a lattice
    Usage
        i = isLattice P
    Inputs
        P:Poset
    Outputs
        i:Boolean
            whether $P$ is a lattice
    Description
        Text
            The poset $P$ is a lattice if every pair of vertices has a unique
            least upper bound and a unique greatest lower bound, i.e., every
            pair of vertices has a unique meet and a unique join.  Equivalently,
            the poset $P$ is a lattice if it is both a lower semilattice and 
            an upper semilattice.

            Clearly, the $n$ @TO "chain"@ and the $n$ @TO "booleanLattice"@ are
            lattices.
        Example
            n = 4;
            isLattice chain n
            B = booleanLattice n;
            isLattice B
        Text
            The middle ranks of the $n$ @TO "booleanLattice"@ are not lattices.
        Example
            isLattice flagPoset(B, {1,2,3})
    SeeAlso
        isBounded
        isLowerSemilattice
        isUpperSemilattice
        joinExists
        meetExists
///

-- isLowerSemilattice
doc ///
    Key
        isLowerSemilattice
        (isLowerSemilattice,Poset)
    Headline
        determines if a poset is a lower (or meet) semilattice
    Usage
        i = isLowerSemilattice P
    Inputs
        P:Poset
    Outputs
        i:Boolean
            whether $P$ is a lower semilattice
    Description
        Text
            The poset $P$ is a lower semilattice if every pair of vertices
            has a unique greatest lower bound (meet).

            Clearly, the $n$ @TO "chain"@ and the $n$ @TO "booleanLattice"@ are
            lower semilattices.
        Example
            n = 4;
            isLowerSemilattice chain n
            B = booleanLattice n;
            isLowerSemilattice B
        Text
            The middle ranks of the $n$ @TO "booleanLattice"@ are not lower semilattices.
        Example
            isLowerSemilattice flagPoset(B, {1,2,3})
        Text
            However, the lower ranks of the $n$ @TO "booleanLattice"@ are non-lattice
            lower semilattices.
        Example
            B' = flagPoset(B, {0,1,2,3});
            isLattice B'
            isLowerSemilattice B'
    SeeAlso
        isLattice
        isUpperSemilattice
        meetExists
///

-- isLowerSemimodular
doc ///
    Key
        isLowerSemimodular
        (isLowerSemimodular,Poset)
    Headline
        determines if a ranked lattice is lower semimodular
    Usage
        i = isLowerSemimodular P 
    Inputs
        P:Poset
            a ranked lattice
    Outputs
        i:Boolean
            whether $P$ is lower semimodular
    Description
        Text
            Let $r$ be the ranking of $P$.  Then $P$ is lower semimodular if for
            every pair of vertices $a$ and $b$, $r(a) + r(b) \leq r(join(a,b)) + r(meet(a,b,))$.

            The $n$ @TO "chain"@ and the $n$ @TO "booleanLattice"@ are
            lower semimodular.
        Example
            n = 4;
            isLowerSemimodular chain n
            isLowerSemimodular booleanLattice n
        Text
            The following lattice is not lower semimodular.
        Example
            P = poset {{1, 2}, {1, 5}, {2, 3}, {2, 4}, {3, 7}, {4, 7}, {5, 4}, {5, 6}, {6, 7}};
            isLattice P
            isLowerSemimodular P
        Text
            This method was ported from John Stembridge's Maple package available at
            @HREF "http://www.math.lsa.umich.edu/~jrs/maple.html#posets"@.  
    SeeAlso
        isLattice
        isModular
        isRanked
        posetJoin
        posetMeet
        rankFunction
///

-- isModular
doc ///
    Key
        isModular
        (isModular,Poset)
    Headline
        determines if a lattice is modular
    Usage
        i = isModular P
    Inputs
        P:Poset
            a ranked lattice
    Outputs
        i:Boolean
            whether $P$ is modular
    Description
        Text
            Let $r$ be the ranking of $P$.  Then $P$ is modular if for
            every pair of vertices $a$ and $b$, $r(a) + r(b) = r(join(a,b)) + r(meet(a,b,))$.
            That is, $P$ is modular if it @TO "isLowerSemimodular"@ and @TO "isUpperSemimodular"@.

            The $n$ @TO "chain"@ and the $n$ @TO "booleanLattice"@ are modular.
        Example
            n = 4;
            isModular chain n
            isModular booleanLattice n
        Text
            The following lattice is not modular.
        Example
            P = poset {{1, 2}, {1, 5}, {2, 3}, {2, 4}, {3, 7}, {4, 7}, {5, 4}, {5, 6}, {6, 7}};
            isLattice P
            isModular P
        Text
            This method uses the methods @TO "isLowerSemimodular"@ and
            @TO "isUpperSemimodular"@, which were ported
            from John Stembridge's Maple package available at
            @HREF "http://www.math.lsa.umich.edu/~jrs/maple.html#posets"@.  
    SeeAlso
        isLattice
        isLowerSemimodular
        isRanked
        isUpperSemimodular
        posetJoin
        posetMeet
        rankFunction
///

-- isRanked
doc ///
    Key
        isRanked
        (isRanked,Poset)
    Headline
        determines if a poset is ranked
    Usage
        i = isRanked P
    Inputs
        P:Poset
    Outputs
        i:Boolean
            whether $P$ is ranked
    Description
        Text
            The poset $P$ is ranked if there exists an integer function $r$ on
            the vertex set of $P$ such that for each $a$ and $b$ in the poset
            if $b$ covers $a$ then $r(b) - r(a) = 1$.

            The $n$ @TO "chain"@ and the $n$ @TO "booleanLattice"@ are ranked.
        Example
            n = 5;
            C = chain n;
            isRanked C
            rankFunction C
            B = booleanLattice n;
            isRanked B
            rankGeneratingFunction C
        Text
            However, the pentagon lattice is not ranked.
        Example
            P = poset {{1,2}, {1,3}, {3,4}, {2,5}, {4,5}};
            isRanked P
        Text
            This method uses the method @TO "rankPoset"@, which was ported
            from John Stembridge's Maple package available at
            @HREF "http://www.math.lsa.umich.edu/~jrs/maple.html#posets"@.  
    SeeAlso
        rankFunction
        rankGeneratingFunction
        rankPoset
///

-- isSperner
doc ///
    Key
        isSperner
        (isSperner,Poset)
    Headline
        determines if a ranked poset has the Sperner property
    Usage
        i = isSperner P
    Inputs
        P:Poset
            a ranked poset
    Outputs
        i:Boolean
            whether $P$ is Sperner
    Description
        Text
            The ranked poset $P$ is Sperner if the maximal size of a rank
            is the @TO "dilworthNumber"@ of $P$.  That is, $P$ is Sperner
            if the maximal size of a rank is the maximal size of an antichain.

            The $n$ @TO "chain"@ and the $n$ @TO "booleanLattice"@ are Sperner.
        Example
            n = 5;
            isSperner chain n
            isSperner booleanLattice n
        Text
            However, the following poset is non-Sperner as it has an antichain
            of size $4$ but both ranks are of size $3$.
        Example
            P = poset {{1,4}, {1,5}, {1,6}, {2,6}, {3,6}};
            isSperner P
            isAntichain(P, {2,3,4,5})
            rankGeneratingFunction P
    SeeAlso
        dilworthNumber
        isRanked
        isStrictSperner
        maximalAntichains
        rankFunction
///

-- isStrictSperner
doc ///
    Key
        isStrictSperner
        (isStrictSperner,Poset)
    Headline
        determines if a ranked poset has the strict Sperner property
    Usage
        i = isStrictSperner P
    Inputs
        P:Poset
            a ranked poset
    Outputs
        i:Boolean
            whether $P$ is strict Sperner
    Description
        Text
            The ranked poset $P$ is strict Sperner if the @TO "maximalAntichains"@
            are the ranks of the poset.

            The $n$ @TO "chain"@ is strict Sperner as the maximal antichains and the
            ranks are singletons.
        Example
            isStrictSperner chain 5
        Text
            The $n$ @TO "booleanLattice"@, for $n \geq 3$, is not strict Sperner as
            it has maximal antichains which are not ranks.
        Example
            B = booleanLattice 3;
            isStrictSperner B
            rankPoset B
            maximalAntichains B
    SeeAlso
        dilworthNumber
        isRanked
        isSperner
        maximalAntichains
        rankFunction
///

-- isUpperSemilattice
doc ///
    Key
        isUpperSemilattice
        (isUpperSemilattice,Poset)
    Headline
        determines if a poset is an upper (or join) semilattice
    Usage
        i = isUpperSemilattice P
    Inputs
        P:Poset
    Outputs
        i:Boolean
            whether $P$ is an upper semilattice
    Description
        Text
            The poset $P$ is an upper semilattice if every pair of vertices
            has a unique least upper bound (join).

            Clearly, the $n$ @TO "chain"@ and the $n$ @TO "booleanLattice"@ are
            upper semilattices.
        Example
            n = 4;
            isUpperSemilattice chain n
            B = booleanLattice n;
            isUpperSemilattice B
        Text
            The middle ranks of the $n$ @TO "booleanLattice"@ are not upper semilattices.
        Example
            isUpperSemilattice flagPoset(B, {1,2,3})
        Text
            However, the upper ranks of the $n$ @TO "booleanLattice"@ are non-lattice
            upper semilattices.
        Example
            B' = flagPoset(B, {1,2,3,4});
            isLattice B'
            isUpperSemilattice B'
    SeeAlso
        isLattice
        isLowerSemilattice
        joinExists
///

-- isUpperSemimodular
doc ///
    Key
        isUpperSemimodular
        (isUpperSemimodular,Poset)
    Headline
        determines if a lattice is upper semimoudlar
    Usage
        i = isUpperSemimodular P
    Inputs
        P:Poset
            a ranked lattice
    Outputs
        i:Boolean
            whether $P$ is upper semimodular
    Description
        Text
            Let $r$ be the ranking of $P$.  Then $P$ is upper semimodular if for
            every pair of vertices $a$ and $b$, $r(a) + r(b) \geq r(join(a,b)) + r(meet(a,b,))$.

            The $n$ @TO "chain"@ and the $n$ @TO "booleanLattice"@ are
            upper semimodular.
        Example
            n = 4;
            isUpperSemimodular chain n
            isUpperSemimodular booleanLattice n
        Text
            The following lattice is not upper semimodular.
        Example
            P = poset {{1, 2}, {1, 3}, {1, 4}, {2, 5}, {2, 6}, {3, 5}, {4, 6}, {5, 7}, {6, 7}};
            isLattice P
            isUpperSemimodular P
        Text
            This method was ported from John Stembridge's Maple package available at
            @HREF "http://www.math.lsa.umich.edu/~jrs/maple.html#posets"@.  
    SeeAlso
        isLattice
        isModular
        isRanked
        posetJoin
        posetMeet
        rankFunction
///

undocumented { "VariableName", (toExternalString,Poset), (toString,Poset) };

------------------------------------------
------------------------------------------
-- Tests
------------------------------------------
------------------------------------------

-- DC2, 1725, 16. August 2011:
-- I think tests should be structured systematically.  I propose two possible styles:
--  * Each test would generate one or more posets and then run most if not all methods on the given poset(s).
--  * Each test only tests one method but on a variety of posets. 

------------------------------------------
------------------------------------------
-- Basic Poset Constructions:
------------------------------------------
------------------------------------------

-- Poset defined by ground set and relations
-- basic Poset constructor
--toExternalString
--hasseDiagram
--isLattice
--comparabilityGraph
TEST ///
P = poset({a,b,c,d},{{a,b},{b,c},{a,d},{d,c}})
Q = toExternalString P
assert(P === value Q)
assert(P === poset({a,b,c,d}, {{a,b},{b,c},{a,d},{d,c}}, matrix {{1, 1, 1, 1}, {0, 1, 1, 0}, {0, 0, 1, 0}, {0, 0, 1,1}}))
assert(P.GroundSet == {a, b, c, d})
assert(P.Relations == {{a, b}, {b, c}, {a, d}, {d, c}})
assert(P.RelationMatrix == map(ZZ^4,ZZ^4,{{1, 1, 1, 1}, {0, 1, 1, 0}, {0, 0, 1, 0}, {0, 0, 1, 1}}))
assert(hasseDiagram P === digraph{{0,1},{0,3},{1,2},{3,2}})
assert((sort coveringRelations P) == (sort P.Relations))
assert(isLattice P)
assert(comparabilityGraph P === graph {{0, 1}, {0, 2}, {0, 3}, {1, 2}, {2, 3}})
assert(comparabilityGraph P === graph apply(edges comparabilityGraph P, toList))
///

-- Poset defined by only relations, lattice
-- basic Poset constructor
--toExternalString
--hasseDiagram
--isLattice
--comparabilityGraph
--rankFunction
TEST ///
P = poset({{a,b},{b,c},{a,d},{d,c}})
Q = toExternalString P
assert(P === value Q)
assert(P === poset({a,b,c,d}, {{a,b},{b,c},{a,d},{d,c}}, matrix {{1, 1, 1, 1}, {0, 1, 1, 0}, {0, 0, 1, 0}, {0, 0, 1,1}}))
assert(P.GroundSet == {a, b, c, d})
assert(P.Relations == {{a, b}, {b, c}, {a, d}, {d, c}})
assert(P.RelationMatrix == map(ZZ^4,ZZ^4,{{1, 1, 1, 1}, {0, 1, 1, 0}, {0, 0, 1, 0}, {0, 0, 1, 1}}))
assert(hasseDiagram P === digraph{{0,1},{0,3},{1,2},{3,2}})
assert((sort coveringRelations P) == (sort P.Relations))
assert(isLattice P)
assert(comparabilityGraph P === graph {{0, 1}, {0, 2}, {0, 3}, {1, 2}, {2, 3}})
assert(comparabilityGraph P === graph apply(edges comparabilityGraph P, toList))
assert(sort rankFunction P == {0, 1, 1, 2})
///

--Poset defined by only relations, not a lattice.
-- basic Poset constructor
--toExternalString
--hasseDiagram
--isLattice
--comparabilityGraph
--rankFunction
--flagPoset
--joinExists & meetExists
TEST /// 
P = poset({{a,b},{b,c},{a,d},{d,c},{d,e}})
Q = toExternalString P
assert(P === value Q)
assert(P === poset({a,b,c,d,e}, {{a,b},{b,c},{a,d},{d,c},{d,e}}, matrix {{1, 1, 1, 1, 1}, {0, 1, 1, 0, 0}, {0, 0, 1, 0, 0}, {0, 0, 1, 1, 1}, {0, 0, 0, 0, 1}}))
assert(P.GroundSet == {a, b, c, d, e})
assert(P.Relations == {{a, b}, {b, c}, {a, d}, {d, c}, {d, e}})
assert(P.RelationMatrix == map(ZZ^5,ZZ^5,{{1, 1, 1, 1, 1}, {0, 1, 1, 0, 0}, {0, 0, 1, 0, 0}, {0, 0, 1, 1, 1}, {0, 0, 0, 0, 1}}))
assert(hasseDiagram P === digraph{{0,1},{0,3},{1,2},{3,2},{3,4}})
assert((sort coveringRelations P) == (sort P.Relations))
assert(not isLattice P)
assert(comparabilityGraph P === graph {{0, 1}, {0, 2}, {0, 3}, {4, 0}, {1, 2}, {2, 3}, {4, 3}})
assert(comparabilityGraph P === graph apply(edges comparabilityGraph P, toList))
assert(sort rankFunction P == {0, 1, 1, 2, 2})
assert(flagPoset(P,{1,2})== poset {{b, c}, {d, c}, {d, e}})
assert(joinExists(P,b,d)== true)
assert(joinExists(P,c,e)==false)
assert(meetExists(P,b,d)==true)
assert(meetExists(P,e,b)==true)
///

--Poset constructed by lcmLattice vs one from relations
--poset isomorphism
--basic Poset constructor
--lcmLattice
TEST /// 
R = QQ[x,y]
P = lcmLattice(ideal(x,y))
Q = poset({{a,b},{b,c},{a,d},{d,c}})
S = toExternalString P
assert(P == Q)
assert(P == value S)
assert(P.GroundSet == {1, y, x, x*y})
assert(P.Relations == {{1, y}, {1, x}, {1, x*y}, {y, x*y}, {x, x*y}})
///

--Poset constructed by booleanLattice vs one from relations
-- basic Poset constructor
--easy isomorphism
--booleanLattice
TEST /// 
P = booleanLattice 2
S = toExternalString P
Q = poset({{a,b},{b,c},{a,d},{d,c}})
assert(P == Q)
assert(P == value S)
assert(P.GroundSet == {"00", "01", "10", "11"})
assert(P.Relations == {{"00", "01"}, {"10", "11"}, {"00", "10"}, {"01", "11"}})
///


--Posets constructed by booleanLattice and lcmLattice
-- booleanLattice/lcmLattice easy tests
--poset isomorphism
--removeIsomorphicPosets
TEST ///
R = QQ[x,y,z,w]
A = booleanLattice 3
B = booleanLattice 4
AA = lcmLattice ideal(x,y,z)
BB = lcmLattice ideal(x,y,z,w)
assert(A == AA)
assert(B == BB)
assert(A =!= B)
assert(AA =!= BB)
assert(# removeIsomorphicPosets({A, adjoinMin(flagPoset(A,{1,2,3})),adjoinMax(flagPoset(A,{0,1,2})),augmentPoset(flagPoset(A,{1,2})),lcmLattice(ideal{x,y,z})}) == 1)
assert(# removeIsomorphicPosets({A, B, adjoinMin(flagPoset(A,{1,2,3})),adjoinMax(flagPoset(A,{0,1,2})),augmentPoset(flagPoset(A,{1,2})),lcmLattice(ideal{x,y,z})}) == 2)
///

--Posets constructed via booleanLattice:
--Lower/Upper SemiLattice

TEST ///
A = booleanLattice 2
assert(A == poset(subsets 2, isSubset))
assert(isLowerSemilattice A)
assert(isUpperSemilattice A)
assert(isDistributive A)
///

--isLattice test
TEST ///
A = booleanLattice 2
B = booleanLattice 3
assert(isLattice A)
assert(isLattice B)
///

TEST ///
B = booleanLattice 3
assert(B == poset(subsets 3, isSubset))
assert(isLowerSemilattice B)
assert(isUpperSemilattice B)
assert(isDistributive B)
assert(hasseDiagram B === digraph{{0, 4}, {0, 1}, {0, 2}, {1, 5}, {1, 3}, {2, 6}, {2, 3}, {3, 7}, {4, 5}, {4, 6}, {5, 7}, {6, 7}})
assert(incomparabilityGraph B === graph({{4, 1}, {1, 2}, {1, 6}, {4, 2}, {5, 2}, {4, 3}, {5, 3}, {6, 3}, {5, 6}}, Singletons=> {0,7}))
R=ring orderComplex B
assert(sub(ideal(flatten entries facets orderComplex B),R) == sub(ideal(v_0*v_4*v_6*v_7,v_0*v_2*v_6*v_7,v_0*v_4*v_5*v_7,v_0*v_1*v_5*v_7,v_0*v_2*v_3*v_7,v_0*v_1*v_3*v_7),R))
assert(sub(ideal(orderComplex B),R) == sub(ideal(v_1*v_2, v_1*v_4, v_2*v_4, v_3*v_4, v_2*v_5, v_3*v_5, v_1*v_6, v_3*v_6, v_5*v_6),R))
assert(closedInterval(B, "001","111") == booleanLattice 2)
assert(openInterval(B, "001","111") == poset({a,b},{}))
assert(dilworthLattice B == poset({{a,b}}))
D=distributiveLattice B
assert(D.cache#OriginalPoset == B)
assert(# chains(D,9) == 48)
assert(hasseDiagram D === digraph new HashTable from {0 => set {1}, 1 => set {2, 3, 6}, 2 => set {4, 7}, 3 => set {4, 8}, 4 => set {5, 9}, 5 => set {10}, 6 => set {7, 8}, 7 => set {9, 11}, 8 => set {9, 14}, 9 => set{10, 12, 15}, 10 => set {13, 16}, 11 => set {12}, 12 => set {13, 17}, 13 => set {18}, 14 => set {15}, 15 => set {16, 17},16 => set {18}, 17 => set {18}, 18 => set {19}, 19 => set {}})
assert(filter(B, {"001", "110"}) == {"001", "011", "101", "111", "110"})
assert(orderIdeal(B, {"001", "110"}) == {"000", "001", "010", "100", "110"})
assert(principalFilter(B,"001") == {"001", "011", "101", "111"})
assert(principalOrderIdeal(B,"001") == {"000", "001"})
assert(subposet(B, filter(B,{"001","110"})) == poset {{001, 011}, {001, 101}, {001, 111}, {011, 111}, {101, 111}, {110, 111}})
assert(subposet(B, orderIdeal(B, {"001", "110"})) == poset {{000, 001}, {000, 010}, {000, 100}, {000, 110}, {010, 110}, {100,110}})
assert(subposet(B,principalFilter(B,"001")) == poset {{001, 011}, {001, 101}, {001, 111}, {011, 111}, {101, 111}})
assert(subposet(B,principalOrderIdeal(B,"001")) == poset {{a,b}})
assert(sort rankFunction B == {0, 1, 1, 1, 2, 2, 2, 3})
assert(flagPoset(B,{1,3}) == poset {{a,d},{b,d},{c,d}})
assert(flagPoset(B,{1,2,3}) == subposet(B,drop(B.GroundSet,1)))
assert(flagPoset(B,{1,3}) == dropElements(B,{"000", "011", "101", "110"}))
assert(flagPoset(B,{1,2,3}) == dropElements(B,{"000"}))
assert(B == indexLabeling B)
assert(B == naturalLabeling B)
r = flatten apply(rankPoset naturalLabeling B, sort)
assert(r == toList(0..#r-1))
assert(adjoinMin(flagPoset(B,{1,2,3})) == B)
assert(adjoinMax(flagPoset(B,{0,1,2})) == B)
assert(augmentPoset(flagPoset(B,{1,2})) == B)
assert(hasseDiagram(diamondProduct(B,B))===digraph new HashTable from {0 => set {1, 2, 4, 8, 9, 11, 22, 23, 25}, 1 => set {3, 5, 15, 29}, 2 => set {3, 6, 16, 30}, 3 => set {7, 17, 31}, 4 => set {5, 6, 18, 32}, 5 => set {7, 19, 33}, 6 => set {7, 20, 34}, 7 => set{21, 35}, 8 => set {10, 12, 15, 36}, 9 => set {10, 13, 16, 37}, 10 => set {14, 17, 38}, 11 => set {12, 13,18, 39}, 12 => set {14, 19, 40}, 13 => set {14, 20, 41}, 14 => set {21, 42}, 15 => set {17, 19, 43}, 16 =>set {17, 20, 44}, 17 => set {21, 45}, 18 => set {19, 20, 46}, 19 => set {21, 47}, 20 => set {21, 48}, 21 => set {49}, 22 => set {24, 26, 29, 36}, 23 => set {24, 27, 30, 37}, 24 => set {28, 31, 38}, 25 => set {26,27, 32, 39}, 26 => set {28, 33, 40}, 27 => set {28, 34, 41}, 28 => set {35, 42}, 29 => set {31, 33, 43}, 30=> set {31, 34, 44}, 31 => set {35, 45}, 32 => set {33, 34, 46}, 33 => set {35, 47}, 34 => set {35, 48}, 35 => set {49}, 36 => set {38, 40, 43}, 37 => set {38, 41, 44}, 38 => set {42, 45}, 39 => set {40, 41, 46}, 40 => set {42, 47}, 41 => set {42, 48}, 42 => set {49}, 43 => set {45, 47}, 44 => set {45, 48}, 45 => set {49}, 46 => set {47, 48}, 47 => set {49}, 48 => set {49}, 49 => set {}})
assert(union(B,B)==B)
C=union(B,naturalLabeling B)
L=connectedComponents C
assert(subposet(C,first L) == subposet(C, last L))
assert(atoms B == {"100", "001", "010"})
assert(compare(B,"100","001") == false)
assert(compare(B,"100","101") == true)
assert(compare(B,"000","111") == true)
assert((sort \ (filtration B)) == (sort \ (rankPoset B)))
assert(joinExists(B,"100","001") == true)
assert(joinExists(B,"100","101") == true)
assert(joinExists(B,"000","111") == true)
assert(joinIrreducibles B == {"000", "001", "100", "010"})
assert(meetExists(B,"100","001") == true)
assert(meetExists(B,"100","101") == true)
assert(meetExists(B,"000","111") == true)
assert(meetIrreducibles B == {"110", "011", "111", "101"})
assert(maximalElements B == {"111"})
assert(minimalElements B == {"000"})
assert(posetJoin(B,"100","001")== {"101"})
assert(posetJoin(B,"110","001")== {"111"})
assert(posetMeet(B,"100","001")== {"000"})
assert(posetMeet(B,"110","011")== {"010"})
assert(rankPoset B == {{"000"}, {"001", "010", "100"}, {"011", "101", "110"}, {"111"}})
assert(allRelations B == {{"000", "000"}, {"000", "001"}, {"000", "010"}, {"000", "011"}, {"000", "100"}, {"000", "101"}, {"000", "110"}, {"000", "111"}, {"001", "001"}, {"001", "011"}, {"001", "101"}, {"001", "111"}, {"010", "010"}, {"010", "011"}, {"010", "110"}, {"010", "111"}, {"011", "011"}, {"011", "111"}, {"100", "100"}, {"100","101"}, {"100", "110"}, {"100", "111"}, {"101", "101"}, {"101", "111"}, {"110", "110"}, {"110", "111"},{"111", "111"}})
assert(coveringRelations B == {{"000", "100"}, {"000", "001"}, {"000", "010"}, {"001", "101"}, {"001", "011"}, {"010", "110"}, {"010", "011"}, {"011", "111"}, {"100", "101"}, {"100", "110"}, {"101", "111"}, {"110", "111"}})
assert(antichains B == {{}, {"000"}, {"001"}, {"001", "010"}, {"001", "010", "100"}, {"001", "100"}, {"001", "110"}, {"010"}, {"010", "100"}, {"010", "101"}, {"011"}, {"011", "100"}, {"011", "101"}, {"011", "101", "110"}, {"011","110"}, {"100"}, {"101"}, {"101", "110"}, {"110"}, {"111"}})
assert(maximalAntichains B == {{"000"}, {"111"}, {"001", "110"}, {"010", "101"}, {"011", "100"}, {"001", "010", "100"}, {"011", "101", "110"}})
assert(maximalChains B == {{"000", "100", "101", "111"}, {"000", "100", "110", "111"}, {"000", "001", "101", "111"}, {"000", "001", "011", "111"}, {"000", "010", "110", "111"}, {"000", "010", "011", "111"}})
assert(chains B == {{}, {"000"}, {"000", "001"}, {"000", "001", "011"}, {"000", "001", "011", "111"}, {"000", "001", "101"}, {"000", "001", "101", "111"}, {"000", "001", "111"}, {"000", "010"}, {"000", "010", "011"}, {"000", "010", "011", "111"}, {"000", "010", "110"}, {"000", "010", "110", "111"}, {"000", "010", "111"}, {"000", "011"}, {"000", "011", "111"}, {"000", "100"}, {"000", "100", "101"}, {"000", "100", "101", "111"}, {"000", "100", "110"}, {"000", "100", "110", "111"}, {"000", "100", "111"}, {"000", "101"}, {"000", "101", "111"}, {"000", "110"}, {"000", "110", "111"}, {"000", "111"}, {"001"}, {"001", "011"}, {"001", "011", "111"}, {"001", "101"}, {"001", "101", "111"}, {"001", "111"}, {"010"}, {"010", "011"}, {"010", "011", "111"}, {"010", "110"}, {"010", "110", "111"}, {"010", "111"}, {"011"}, {"011", "111"}, {"100"}, {"100", "101"}, {"100", "101", "111"}, {"100", "110"}, {"100", "110", "111"}, {"100", "111"}, {"101"}, {"101", "111"}, {"110"}, {"110", "111"}, {"111"}})
assert(flagChains(B,{1,2,3}) == {{"001", "011", "111"}, {"010", "011", "111"}, {"001", "101", "111"}, {"100", "101", "111"}, {"010", "110", "111"}, {"100", "110", "111"}})
assert(chains B == sort join({{}},flatten apply(subsets({0,1,2,3}), s-> flagChains(B,s))))
assert(isAntichain(B,{"001","100"})==true)
assert(isAntichain(B,{"111","100"})==false)
assert(# linearExtensions B == 48)
assert(toString characteristicPolynomial B === "q^3-3*q^2+3*q-1")
assert(toString flagfPolynomial B === "6*q_0*q_1*q_2*q_3+6*q_0*q_1*q_2+3*q_0*q_1*q_3+3*q_0*q_2*q_3+6*q_1*q_2*q_3+3*q_0*q_1+3*q_0*q_2+6*q_1*q_2+q_0*q_3+3*q_1*q_3+3*q_2*q_3+q_0+3*q_1+3*q_2+q_3+1")
assert(toString flaghPolynomial B === "q_1*q_2+2*q_1+2*q_2+1")
assert(toString fPolynomial B === "6*q^4+18*q^3+19*q^2+8*q+1")
assert(toString hPolynomial B === "q^2+4*q+1")
assert(greeneKleitmanPartition B === new Partition from {4,2,2})
assert(moebiusFunction B === new HashTable from {("010","010") => 1, ("010","011") => -1, ("110","010") => 0, ("000","000") => 1,
      ("011","110") => 0, ("110","011") => 0, ("000","001") => -1, ("111","110") => 0, ("011","111") => -1,
      ("100","000") => 0, ("001","100") => 0, ("111","111") => 1, ("100","001") => 0, ("001","101") => -1,
      ("101","100") => 0, ("101","101") => 1, ("000","010") => -1, ("011","000") => 0, ("000","011") => 1,
      ("100","010") => 0, ("010","100") => 0, ("011","001") => 0, ("111","000") => 0, ("001","110") => 0,
      ("010","101") => 0, ("100","011") => 0, ("110","100") => 0, ("110","101") => 0, ("101","110") => 0,
      ("111","001") => 0, ("001","111") => 1, ("101","111") => -1, ("011","010") => 0, ("010","110") => -1,
      ("011","011") => 1, ("110","110") => 1, ("111","010") => 0, ("010","111") => 1, ("001","000") => 0,
      ("110","111") => -1, ("111","011") => 0, ("000","100") => -1, ("101","000") => 0, ("001","001") => 1,
      ("000","101") => 1, ("100","100") => 1, ("101","001") => 0, ("100","101") => -1, ("010","000") => 0,
      ("001","010") => 0, ("010","001") => 0, ("000","110") => 1, ("110","000") => 0, ("001","011") => -1,
      ("101","010") => 0, ("011","100") => 0, ("000","111") => -1, ("110","001") => 0, ("100","110") => -1,
      ("100","111") => 1, ("111","100") => 0, ("011","101") => 0, ("101","011") => 0, ("111","101") => 0})
assert(toString rankGeneratingFunction B === "q^3+3*q^2+3*q+1")
assert(toString zetaPolynomial B == "q^3")
assert(dilworthNumber B === 3)
assert(isAtomic B == true)
assert(isBounded B == true)
assert(isConnected B == true)
assert(isDistributive B == true)
assert(isEulerian B == true)
assert(isGeometric B == true)
assert(isGraded B == true)
assert(isLattice B == true)
assert(isLowerSemilattice B == true)
assert(isLowerSemimodular B == true)
assert(isModular B == true)
assert(isRanked B == true)
assert(isSperner B == true)
assert(isStrictSperner B == false)
assert(isUpperSemilattice B == true)
assert(isUpperSemimodular B == true)

///

--Tests for chains
TEST ///
B = chain 5
assert(isLowerSemilattice B)
assert(isUpperSemilattice B)
assert(isDistributive B)
assert(hasseDiagram B === digraph{{0, 1}, {1, 2}, {2, 3}, {3, 4}})
assert(incomparabilityGraph B === graph({}, Singletons=> {0,1,2,3,4}))
R=ring orderComplex B
assert(sub(ideal(flatten entries facets orderComplex B),R) == sub(ideal(v_0*v_1*v_2*v_3*v_4),R))
assert(sub(ideal(orderComplex B),R) == sub(ideal(),R))
assert(closedInterval(B,1,4) == chain 4)
assert(openInterval(B,1,4) == chain 2)
assert(dilworthLattice B == poset({{{1}, {2}}, {{1}, {3}}, {{1}, {4}}, {{1}, {5}}, {{2}, {3}}, {{2}, {4}}, {{2}, {5}}, {{3}, {4}}, {{3},{5}}, {{4}, {5}}}))
D=distributiveLattice B
assert(D.cache#OriginalPoset == B)
assert(# chains(D,3) == 20)
assert(# chains(D,6) == 1)
assert(hasseDiagram D === digraph new HashTable from {0 => set {1}, 1 => set {2}, 2 => set {3}, 3 => set {4}, 4 => set {5}, 5 => set {}})
assert(filter(B,{3}) == {3,4,5})
assert(filter(B,{1}) == B.GroundSet)
assert(orderIdeal(B,{3}) == {1,2,3})
assert(orderIdeal(B,{5}) == B.GroundSet)
assert(principalFilter(B,3) == {3,4,5})
assert(principalOrderIdeal(B,3) == {1,2,3})
assert(subposet(B, filter(B,{3})) == poset {{3, 4}, {3, 5}, {4, 5}})
assert(subposet(B, orderIdeal(B,{3})) == poset {{1,2},{2,3},{1,3}})
assert(subposet(B, filter(B,{3})) == chain 3)
assert(subposet(B, orderIdeal(B,{3})) == chain 3)
assert(subposet(B,principalFilter(B,3)) == poset {{3, 4}, {3, 5}, {4, 5}})
assert(subposet(B,principalOrderIdeal(B,3)) == poset {{1,2},{2,3},{1,3}})
assert(sort rankFunction B == {0,1,2,3,4})
assert(flagPoset(B,{1,3}) == poset {{2,4}})
assert(flagPoset(B,{1,2,3}) == chain 3)
assert(flagPoset(B,{1,3}) == dropElements(B,{1,3,5}))
assert(flagPoset(B,{1,2,3}) == dropElements(B,{1,5}))
assert(B == indexLabeling B)
assert(B == naturalLabeling B)
r = flatten apply(rankPoset naturalLabeling B, sort)
assert(r == toList(0..#r-1))
assert(adjoinMin(flagPoset(B,{1,2,3,4})) == B)
assert(adjoinMax(flagPoset(B,{1,2,3,4})) == B)
assert(augmentPoset(flagPoset(B,{1,2,3})) == B)
assert(hasseDiagram(diamondProduct(B,B))===digraph new HashTable from {0 => set {1}, 1 => set {2, 5}, 2 => set {3, 6}, 3 => set {4, 7}, 4 => set {8}, 5 => set {6, 9}, 6 => set {7, 10}, 7 => set {8, 11}, 8 => set {12}, 9 => set {10, 13}, 10 => set {11, 14}, 11 => set {12, 15}, 12 => set {16}, 13 => set {14}, 14 => set {15}, 15 => set {16}, 16 => set {}})
assert(union(B,B)==B)
assert(atoms B == {2})
assert(compare(B,1,2) == true)
assert(compare(B,1,5) == true)
assert((sort \ (filtration B)) == (sort \ (rankPoset B)))
assert(joinExists(B,1,2) == true)
assert(joinIrreducibles B == {1,2,3,4,5})
assert(meetExists(B,1,5) == true)
assert(meetExists(B,1,2) == true)
assert(meetIrreducibles B == {1,2,3,4,5})
assert(maximalElements B == {5})
assert(minimalElements B == {1})
assert(posetJoin(B,1,2)== {2})
assert(posetJoin(B,1,5)== {5})
assert(posetMeet(B,1,2)== {1})
assert(posetMeet(B,1,5)== {1})
assert(rankPoset B == {{1}, {2}, {3}, {4}, {5}})
assert(allRelations B == {{1,1},{1,2},{1,3},{1,4},{1,5},{2,2},{2,3},{2,4},{2,5},{3,3},{3,4},{3,5},{4,4},{4,5},{5,5}})
assert(coveringRelations B == {{1,2},{2,3},{3,4},{4,5}})
assert(antichains B == {{}, {1}, {2}, {3}, {4}, {5}})
assert(maximalAntichains B == {{1}, {2}, {3}, {4}, {5}})
maximalChains B
assert(maximalChains B == {{1, 2, 3, 4, 5}})
assert(chains B == {{}, {1}, {1, 2}, {1, 2, 3}, {1, 2, 3, 4}, {1, 2, 3, 4, 5}, {1, 2, 3, 5}, {1, 2, 4}, {1, 2, 4, 5}, {1, 2, 5}, {1, 3}, {1, 3, 4}, {1, 3, 4, 5}, {1, 3, 5}, {1, 4}, {1, 4, 5}, {1, 5}, {2}, {2, 3}, {2, 3, 4}, {2, 3, 4, 5}, {2, 3, 5}, {2, 4}, {2, 4, 5}, {2, 5}, {3}, {3, 4}, {3, 4, 5}, {3, 5}, {4}, {4, 5}, {5}})
assert(flagChains(B,{1,2,3}) == {{2, 3, 4}})
assert(chains B == sort join({{}},flatten apply(subsets({0,1,2,3,4}), s-> flagChains(B,s))))
assert(isAntichain(B,{1})==true)
assert(isAntichain(B,{1,2})==false)
assert(# linearExtensions B == 1)
assert(toString characteristicPolynomial B === "q^4-q^3")
assert(toString flagfPolynomial B === "q_0*q_1*q_2*q_3*q_4+q_0*q_1*q_2*q_3+q_0*q_1*q_2*q_4+q_0*q_1*q_3*q_4+q_0*q_2*q_3*q_4+q_1*q_2*q_3*q_4+q_0*q_1*q_2+q_0*q_1*q_3+q_0*q_2*q_3+q_1*q_2*q_3+q_0*q_1*q_4+q_0*q_2*q_4+q_1*q_2*q_4+q_0*q_3*q_4+q_1*q_3*q_4+q_2*q_3*q_4+q_0*q_1+q_0*q_2+q_1*q_2+q_0*q_3+q_1*q_3+q_2*q_3+q_0*q_4+q_1*q_4+q_2*q_4+q_3*q_4+q_0+q_1+q_2+q_3+q_4+1")
assert(toString flaghPolynomial B === "1")
assert(toString fPolynomial B === "q^5+5*q^4+10*q^3+10*q^2+5*q+1")
assert(toString hPolynomial B === "1")
assert(greeneKleitmanPartition B === new Partition from {5})
assert(moebiusFunction B === new HashTable from {(5,2) => 0, (4,3) => 0, (2,5) => 0, (3,4) => -1, (3,5) => 0, (5,3) => 0, (4,4) => 1,
       (4,5) => -1, (5,4) => 0, (5,5) => 1, (1,1) => 1, (2,1) => 0, (1,2) => -1, (3,1) => 0, (2,2) => 1, (1,3)
       => 0, (1,4) => 0, (3,2) => 0, (2,3) => -1, (4,1) => 0, (4,2) => 0, (5,1) => 0, (1,5) => 0, (2,4) => 0,
       (3,3) => 1})
assert(toString rankGeneratingFunction B === "q^4+q^3+q^2+q+1")
assert(toString zetaPolynomial B == "(1/24)*q^4+(1/4)*q^3+(11/24)*q^2+(1/4)*q")
assert(dilworthNumber B === 1)
assert(isAtomic B == false)
assert(isBounded B == true)
assert(isConnected B == true)
assert(isDistributive B == true)
assert(isEulerian B == false)
assert(isGeometric B == false)
assert(isGraded B == true)
assert(isLattice B == true)
assert(isLowerSemilattice B == true)
assert(isLowerSemimodular B == true)
assert(isModular B == true)
assert(isRanked B == true)
assert(isSperner B == true)
assert(isStrictSperner B == true)
assert(isUpperSemilattice B == true)
assert(isUpperSemimodular B == true)

///





--Tests for divisorPoset(ZZ)

TEST ///
P = divisorPoset 30
assert(P == poset(subsets 3, isSubset))
B = divisorPoset 96
assert(isLowerSemilattice B)
assert(isUpperSemilattice B)
assert(isDistributive B)
assert(hasseDiagram B === digraph {{0, 1}, {0, 2}, {1, 4}, {1, 3}, {2, 4}, {3, 5}, {3, 6}, {4, 6}, {5, 8}, {5, 7}, {6, 8}, {7, 9}, {7, 10}, {8, 10}, {9, 11}, {10,11}})
assert(incomparabilityGraph B === graph({{1, 2},{2, 9}, {2, 3}, {2, 5}, {2, 7}, {3, 4}, {4, 5}, {4, 9}, {4, 7}, {5, 6}, {6, 9}, {6, 7}, {7, 8}, {8, 9}, {9, 10}}, Singletons =>{0,11}))
R=ring orderComplex B
assert(sub(ideal(flatten entries facets orderComplex B),R) == sub(ideal(v_0*v_2*v_4*v_6*v_8*v_10*v_11,v_0*v_1*v_4*v_6*v_8*v_10*v_11,v_0*v_1*v_3*v_6*v_8*v_10*v_11,v_0*v_1*v_3*v_5*v_8*v_10*v_11,v_0*v_1*v_3*v_5*v_7*v_10*v_11,v_0*v_1*v_3*v_5*v_7*v_9*v_11),R))
assert(sub(ideal(orderComplex B),R) == sub(ideal(v_1*v_2,v_2*v_3,v_3*v_4,v_2*v_5,v_4*v_5,v_5*v_6,v_2*v_7,v_4*v_7,v_6*v_7,v_7*v_8,v_2*v_9,v_4*v_9,v_6*v_9,v_8*v_9,v_9*v_10),R))
assert(closedInterval(B,2,24) == poset({{2, 4}, {2, 6}, {2, 8}, {2, 12}, {2, 24}, {4, 8}, {4, 12}, {4,24}, {6, 12}, {6, 24}, {8, 24}, {12, 24}}))
assert(openInterval(B,2,24) == poset({{4, 8}, {4, 12}, {6, 12}}))
assert(dilworthLattice B == poset({{{2, 3}, {3, 4}}, {{3, 32}, {6, 32}}, {{3, 4}, {4, 6}}, {{3, 4},
      {3, 8}}, {{3, 8}, {3, 16}}, {{3, 8}, {6, 8}}, {{3, 16}, {6, 16}},
      {{3, 16}, {3, 32}}, {{4, 6}, {6, 8}}, {{6, 32}, {12, 32}}, {{6,
      8}, {6, 16}}, {{6, 8}, {8, 12}}, {{6, 16}, {6, 32}}, {{6, 16},
      {12, 16}}, {{8, 12}, {12, 16}}, {{12, 32}, {24, 32}}, {{12, 16},
      {16, 24}}, {{12, 16}, {12, 32}}, {{16, 24}, {24, 32}}, {{24, 32},
      {32, 48}}}))

D=distributiveLattice B
assert(D.cache#OriginalPoset == B)
assert(# chains(D,12) == 1386)
assert(# chains(D,13) == 132)
assert(hasseDiagram D === digraph new HashTable from {0 => set {1}, 1 => set {2, 3}, 2 => set {4,5}, 3 => set {4}, 4 => set {6, 7}, 5 => set {6, 9}, 6 => set {8,10}, 7 => set {8}, 8 => set {11, 12}, 9 => set {10, 14}, 10 => set{11, 15}, 11 => set {13, 16}, 12 => set {13}, 13 => set {17, 18}, 14 => set {15, 20}, 15 => set {16, 21}, 16 => set {17, 22}, 17 =>set {19, 23}, 18 => set {19}, 19 => set {24, 25}, 20 => set {21}, 21 => set {22}, 22 => set {23}, 23 => set {24}, 24 => set {26}, 25=> set {26}, 26 => set {27}, 27 => set {}})
assert(sort filter(B, {4,6}) == {4, 6, 8, 12, 16, 24, 32, 48, 96})
assert(sort orderIdeal(B, {4,6}) == {1, 2, 3, 4, 6})
assert(sort principalFilter(B,4) == {4, 8, 12, 16, 24, 32, 48, 96})
assert(sort principalOrderIdeal(B,4) == {1, 2, 4})
assert(subposet(B, filter(B,{4,6})) == poset {{4, 8}, {4, 12}, {6, 12}, {8, 16}, {8, 24}, {12, 24}, {16, 32}, {16, 48}, {24, 48}, {32, 96}, {48, 96}})
assert(subposet(B, orderIdeal(B, {4,6})) == poset {{1, 2}, {1, 3}, {2, 6}, {2, 4}, {3, 6}})
assert(subposet(B,principalFilter(B,4)) == poset {{4, 8}, {4, 12}, {8, 24}, {8, 16}, {12, 24}, {16, 32}, {16, 48}, {24, 48}, {32, 96}, {48, 96}})
assert(subposet(B,principalOrderIdeal(B,4)) == poset {{1, 2}, {2, 4}})
assert(sort rankFunction B == {0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6})
assert(flagPoset(B,{1,3,5}) == poset {{2, 8}, {2, 12}, {3, 12}, {8, 32}, {8, 48}, {12, 48}})
assert(flagPoset(B,{0,1,2,3}) == subposet(B,{1, 2, 3, 4, 6, 8, 12}))

assert(flagPoset(B,{1,3}) == dropElements(B,{1, 4, 6, 16, 24, 32, 48, 96}))
assert(flagPoset(B,{1,2,3}) == dropElements(B,{1, 16, 24, 32, 48, 96}))
assert(B == indexLabeling B)
assert(B == naturalLabeling B)
r = flatten apply(rankPoset naturalLabeling B, sort)
assert(r == toList(0..#r-1))
assert(adjoinMin(flagPoset(B,{1,2,3,4,5,6})) == B)
assert(adjoinMax(flagPoset(B,{0,1,2,3,4,5})) == B)
assert(augmentPoset(flagPoset(B,{1,2,3,4,5})) == B)
--Removed for time purposes (slow!)
--assert(hasseDiagram(diamondProduct(B,B))===digraph new HashTable from {0 => set {1, 2, 12, 13}, 1 => set {3, 4, 23, 34}, 2 => set {4, 24, 35}, 3 => set {5, 6, 25, 36}, 4 => set {6, 26, 37}, 5 => set {7, 8, 27, 38}, 6 => set {8, 28, 39}, 7 => set{9, 10, 29, 40}, 8 => set {10, 30, 41}, 9 => set {11, 31, 42}, 10 => set {11, 32, 43}, 11 => set {33, 44}, 12 => set {14, 15, 34}, 13 => set {15, 35}, 14 => set {16, 17, 36}, 15 => set {17, 37}, 16 => set {18, 19, 38}, 17 => set {19, 39}, 18 => set {20, 21, 40}, 19 => set {21, 41}, 20 => set {22, 42}, 21 => set {22, 43}, 22 => set {44}, 23 => set {25, 26, 45, 56}, 24 => set {26, 46, 57}, 25 => set {27, 28, 47, 58}, 26 => set {28, 48, 59}, 27 => set {29, 30, 49, 60}, 28 => set {30, 50, 61}, 29 => set {31, 32, 51, 62}, 30 => set {32, 52, 63}, 31 => set {33, 53, 64}, 32 => set {33, 54, 65}, 33 => set {55, 66}, 34 => set {36, 37, 56}, 35 => set {37, 57}, 36 => set {38, 39, 58}, 37 => set {39, 59}, 38 => set {40, 41, 60}, 39 => set {41, 61}, 40 => set {42, 43, 62}, 41 => set {43, 63}, 42 => set {44, 64}, 43 => set {44, 65}, 44 => set {66}, 45 => set {47, 48, 67, 78}, 46 => set {48, 68, 79}, 47 => set {49, 50, 69, 80}, 48 => set {50, 70, 81}, 49 => set {51, 52, 71, 82}, 50 => set {52, 72, 83}, 51 => set {53, 54, 73, 84}, 52 => set {54, 74, 85}, 53 => set {55, 75, 86}, 54 => set {55, 76, 87}, 55 => set {77, 88}, 56 => set {58, 59, 78}, 57 => set {59, 79}, 58 => set {60, 61, 80}, 59 => set {61, 81}, 60 => set {62, 63, 82}, 61 => set {63, 83}, 62 => set {64, 65, 84}, 63 => set {65, 85}, 64 => set {66, 86}, 65 => set {66, 87}, 66 => set {88}, 67 => set {69, 70, 89, 100}, 68 => set {70, 90, 101}, 69 => set {71, 72, 91, 102}, 70 => set {72, 92, 103}, 71 => set {73, 74, 93, 104}, 72 => set {74, 94, 105}, 73 => set {75, 76, 95, 106}, 74 => set {76, 96, 107}, 75 => set {77, 97, 108}, 76 => set {77, 98, 109}, 77 => set {99, 110}, 78 => set {80, 81, 100}, 79 => set {81, 101}, 80 => set {82, 83, 102}, 81 => set {83, 103}, 82 => set {84, 85, 104}, 83 => set {85, 105}, 84 => set {86, 87, 106}, 85 => set {87, 107}, 86 => set {88, 108}, 87 => set {88, 109}, 88 => set {110}, 89 => set {91, 92, 111}, 90 => set {92, 112}, 91 => set {93, 94, 113}, 92 => set {94, 114}, 93 => set {95, 96, 115}, 94 => set {96, 116}, 95 => set {97, 98, 117}, 96 => set {98, 118}, 97 => set {99, 119}, 98 => set {99, 120}, 99 => set {121}, 100 => set {102, 103, 111}, 101 => set {103, 112}, 102 => set {104, 105, 113}, 103 => set {105, 114}, 104 => set {106, 107, 115}, 105 => set {107, 116}, 106 => set {108, 109, 117}, 107 => set {109, 118}, 108 => set {110, 119}, 109 => set {110, 120}, 110 => set {121}, 111 => set {113, 114}, 112 => set {114}, 113 => set {115, 116}, 114 => set {116}, 115 => set {117, 118}, 116 => set {118}, 117 => set {119, 120}, 118 => set {120}, 119 => set {121}, 120 => set {121}, 121 => set {}})
assert(union(B,B)==B)
assert(atoms B == {2,3})
assert(compare(B,3,4) == false)
assert(compare(B,3,6) == true)
assert(compare(B,3,48) == true)
assert((sort \ (filtration B)) == (sort \ (rankPoset B)))
assert(joinExists(B,2,3) == true)
assert(joinExists(B,3,6) == true)
assert(joinExists(B,3,8) == true)
assert(sort joinIrreducibles B == {1, 2, 3, 4, 8, 16, 32})
assert(meetExists(B,16,3) == true)
assert(meetExists(B,32,24) == true)
assert(meetExists(B,32,16) == true)
assert(sort meetIrreducibles B == {3, 6, 12, 24, 32, 48, 96})
assert(maximalElements B == {96})
assert(minimalElements B == {1})
assert(posetJoin(B,2,3)== {6})
assert(posetJoin(B,3,6)== {6})
assert(posetJoin(B,3,8)== {24})
assert(posetMeet(B,16,3)== {1})
assert(posetMeet(B,32,24)== {gcd(24,32)})
assert(posetMeet(B,32,16)== {16})
assert(rankPoset B == {{1}, {2, 3}, {4, 6}, {8, 12}, {16, 24}, {32, 48}, {96}})
assert(allRelations B == {{1, 1}, {1, 2}, {1, 3}, {1, 4}, {1, 6}, {1, 8}, {1, 12}, {1,16}, {1, 24}, {1, 32}, {1, 48}, {1, 96}, {2, 2}, {2, 4}, {2, 6}, {2, 8}, {2, 12}, {2, 16}, {2, 24}, {2, 32}, {2, 48}, {2, 96}, {3, 3}, {3, 6}, {3, 12}, {3, 24}, {3, 48}, {3, 96}, {4, 4}, {4, 8}, {4, 12}, {4, 16}, {4, 24}, {4, 32}, {4, 48}, {4, 96}, {6, 6}, {6, 12}, {6, 24}, {6, 48}, {6, 96}, {8, 8}, {8, 16}, {8, 24}, {8,32}, {8, 48}, {8, 96}, {12, 12}, {12, 24}, {12, 48}, {12, 96}, {16, 16}, {16, 32}, {16, 48}, {16, 96}, {24, 24}, {24, 48}, {24, 96}, {32, 32}, {32, 96}, {48, 48}, {48, 96}, {96, 96}})
assert(coveringRelations B == {{1, 2}, {1, 3}, {2, 6}, {2, 4}, {3, 6}, {4, 8}, {4, 12}, {6, 12}, {8, 24}, {8, 16}, {12, 24}, {16, 32}, {16, 48}, {24, 48}, {32, 96}, {48, 96}})
assert(antichains B == {{}, {1}, {2}, {2, 3}, {3}, {3, 4}, {3, 8}, {3, 16}, {3, 32}, {4}, {4, 6}, {6}, {6, 8}, {6, 16}, {6, 32}, {8}, {8, 12}, {12}, {12, 16}, {12, 32}, {16}, {16, 24}, {24}, {24, 32}, {32}, {32, 48}, {48}, {96}})
assert(maximalAntichains B == {{1}, {96}, {2, 3}, {3, 32}, {3, 4}, {3, 8}, {3, 16}, {4, 6}, {6, 32}, {6, 8}, {6, 16}, {8, 12}, {12, 32}, {12, 16}, {16, 24}, {24, 32}, {32, 48}})
assert(maximalChains B == {{1, 2, 6, 12, 24, 48, 96}, {1, 2, 4, 8, 24, 48, 96}, {1, 2, 4, 8, 16, 32, 96}, {1, 2, 4, 8, 16, 48, 96}, {1, 2, 4, 12, 24, 48, 96}, {1, 3, 6, 12, 24, 48, 96}})
assert(chains B == {{}, {1}, {1, 2}, {1, 2, 4}, {1, 2, 4, 8}, {1, 2, 4, 8, 16}, {1, 2, 4, 8, 16, 32}, {1, 2, 4, 8, 16, 32, 96}, {1, 2, 4, 8, 16, 48}, {1, 2, 4, 8, 16, 48, 96}, {1, 2, 4, 8, 16, 96}, {1, 2, 4, 8, 24}, {1, 2, 4, 8, 24, 48}, {1, 2, 4, 8, 24, 48, 96}, {1, 2, 4, 8, 24, 96}, {1, 2, 4, 8, 32}, {1, 2, 4, 8, 32, 96}, {1, 2, 4, 8, 48}, {1, 2, 4, 8, 48, 96}, {1, 2, 4, 8, 96}, {1, 2, 4, 12}, {1, 2, 4, 12, 24}, {1, 2, 4, 12, 24, 48}, {1, 2, 4, 12, 24, 48, 96}, {1, 2, 4, 12, 24, 96}, {1, 2, 4, 12, 48}, {1, 2, 4, 12, 48, 96}, {1, 2, 4, 12, 96}, {1, 2, 4, 16}, {1, 2, 4, 16, 32}, {1, 2, 4, 16, 32, 96}, {1, 2, 4, 16, 48}, {1, 2, 4, 16, 48, 96}, {1, 2, 4, 16, 96}, {1, 2, 4, 24}, {1, 2, 4, 24, 48}, {1, 2, 4, 24, 48, 96}, {1, 2, 4, 24, 96}, {1, 2, 4, 32}, {1, 2, 4, 32, 96}, {1, 2, 4, 48}, {1, 2, 4, 48, 96}, {1, 2, 4, 96}, {1, 2, 6}, {1, 2, 6, 12}, {1, 2, 6, 12, 24}, {1, 2, 6, 12, 24, 48}, {1, 2, 6, 12, 24, 48, 96}, {1, 2, 6, 12, 24, 96}, {1, 2, 6, 12, 48}, {1, 2, 6, 12, 48, 96}, {1, 2, 6, 12, 96}, {1, 2, 6, 24}, {1, 2, 6, 24, 48}, {1, 2, 6, 24, 48, 96}, {1, 2, 6, 24, 96}, {1, 2, 6, 48}, {1, 2, 6, 48, 96}, {1, 2, 6, 96}, {1, 2, 8}, {1, 2, 8, 16}, {1, 2, 8, 16, 32}, {1, 2, 8, 16, 32, 96}, {1, 2, 8, 16, 48}, {1, 2, 8, 16, 48, 96}, {1, 2, 8, 16, 96}, {1, 2, 8, 24}, {1, 2, 8, 24, 48}, {1, 2, 8, 24, 48, 96}, {1, 2, 8, 24, 96}, {1, 2, 8, 32}, {1, 2, 8, 32, 96}, {1, 2, 8, 48}, {1, 2, 8, 48, 96}, {1, 2, 8, 96}, {1, 2, 12}, {1, 2, 12, 24}, {1, 2, 12, 24, 48}, {1, 2, 12, 24, 48, 96}, {1, 2, 12, 24, 96}, {1, 2, 12, 48}, {1, 2, 12, 48, 96}, {1, 2, 12, 96}, {1, 2, 16}, {1, 2, 16, 32}, {1, 2, 16, 32, 96}, {1, 2, 16, 48}, {1, 2, 16, 48, 96}, {1, 2, 16, 96}, {1, 2, 24}, {1, 2, 24, 48}, {1, 2, 24, 48, 96}, {1, 2, 24, 96}, {1, 2, 32}, {1, 2, 32, 96}, {1, 2, 48}, {1, 2, 48, 96}, {1, 2, 96}, {1, 3}, {1, 3, 6}, {1, 3, 6, 12}, {1, 3, 6, 12, 24}, {1, 3, 6, 12, 24, 48}, {1, 3, 6, 12, 24, 48, 96}, {1, 3, 6, 12, 24, 96}, {1, 3, 6, 12, 48}, {1, 3, 6, 12, 48, 96}, {1, 3, 6, 12, 96}, {1, 3, 6, 24}, {1, 3, 6, 24, 48}, {1, 3, 6, 24, 48, 96}, {1, 3, 6, 24, 96}, {1, 3, 6, 48}, {1, 3, 6, 48, 96}, {1, 3, 6, 96}, {1, 3, 12}, {1, 3, 12, 24}, {1, 3, 12, 24, 48}, {1, 3, 12, 24, 48, 96}, {1, 3, 12, 24, 96}, {1, 3, 12, 48}, {1, 3, 12, 48, 96}, {1, 3, 12, 96}, {1, 3, 24}, {1, 3, 24, 48}, {1, 3, 24, 48, 96}, {1, 3, 24, 96}, {1, 3, 48}, {1, 3, 48, 96}, {1, 3, 96}, {1, 4}, {1, 4, 8}, {1, 4, 8, 16}, {1, 4, 8, 16, 32}, {1, 4, 8, 16, 32, 96}, {1, 4, 8, 16, 48}, {1, 4, 8, 16, 48, 96}, {1, 4, 8, 16, 96}, {1, 4, 8, 24}, {1, 4, 8, 24, 48}, {1, 4, 8, 24, 48, 96}, {1, 4, 8, 24, 96}, {1, 4, 8, 32}, {1, 4, 8, 32, 96}, {1, 4, 8, 48}, {1, 4, 8, 48, 96}, {1, 4, 8, 96}, {1, 4, 12}, {1, 4, 12, 24}, {1, 4, 12, 24, 48}, {1, 4, 12, 24, 48, 96}, {1, 4, 12, 24, 96}, {1, 4, 12, 48}, {1, 4, 12, 48, 96}, {1, 4, 12, 96}, {1, 4, 16}, {1, 4, 16, 32}, {1, 4, 16, 32, 96}, {1, 4, 16, 48}, {1, 4, 16, 48, 96}, {1, 4, 16, 96}, {1, 4, 24}, {1, 4, 24, 48}, {1, 4, 24, 48, 96}, {1, 4, 24, 96}, {1, 4, 32}, {1, 4, 32, 96}, {1, 4, 48}, {1, 4, 48, 96}, {1, 4, 96}, {1, 6}, {1, 6, 12}, {1, 6, 12, 24}, {1, 6, 12, 24, 48}, {1, 6, 12, 24, 48, 96}, {1, 6, 12, 24, 96}, {1, 6, 12, 48}, {1, 6, 12, 48, 96}, {1, 6, 12, 96}, {1, 6, 24}, {1, 6, 24, 48}, {1, 6, 24, 48, 96}, {1, 6, 24, 96}, {1, 6, 48}, {1, 6, 48, 96}, {1, 6, 96}, {1, 8}, {1, 8, 16}, {1, 8, 16, 32}, {1, 8, 16, 32, 96}, {1, 8, 16, 48}, {1, 8, 16, 48, 96}, {1, 8, 16, 96}, {1, 8, 24}, {1, 8, 24, 48}, {1, 8, 24, 48, 96}, {1, 8, 24, 96}, {1, 8, 32}, {1, 8, 32, 96}, {1, 8, 48}, {1, 8, 48, 96}, {1, 8, 96}, {1, 12}, {1, 12, 24}, {1, 12, 24, 48}, {1, 12, 24, 48, 96}, {1, 12, 24, 96}, {1, 12, 48}, {1, 12, 48, 96}, {1, 12, 96}, {1, 16}, {1, 16, 32}, {1, 16, 32, 96}, {1, 16, 48}, {1, 16, 48, 96}, {1, 16, 96}, {1, 24}, {1, 24, 48}, {1, 24, 48, 96}, {1, 24, 96}, {1, 32}, {1, 32, 96}, {1, 48}, {1, 48, 96}, {1, 96}, {2}, {2, 4}, {2, 4, 8}, {2, 4, 8, 16}, {2, 4, 8, 16, 32}, {2, 4, 8, 16, 32, 96}, {2, 4, 8, 16, 48}, {2, 4, 8, 16, 48, 96}, {2, 4, 8, 16, 96}, {2, 4, 8, 24}, {2, 4, 8, 24, 48}, {2, 4, 8, 24, 48, 96}, {2, 4, 8, 24, 96}, {2, 4, 8, 32}, {2, 4, 8, 32, 96}, {2, 4, 8, 48}, {2, 4, 8, 48, 96}, {2, 4, 8, 96}, {2, 4, 12}, {2, 4, 12, 24}, {2, 4, 12, 24, 48}, {2, 4, 12, 24, 48, 96}, {2, 4, 12, 24, 96}, {2, 4, 12, 48}, {2, 4, 12, 48, 96}, {2, 4, 12, 96}, {2, 4, 16}, {2, 4, 16, 32}, {2, 4, 16, 32, 96}, {2, 4, 16, 48}, {2, 4, 16, 48, 96}, {2, 4, 16, 96}, {2, 4, 24}, {2, 4, 24, 48}, {2, 4, 24, 48, 96}, {2, 4, 24, 96}, {2, 4, 32}, {2, 4, 32, 96}, {2, 4, 48}, {2, 4, 48, 96}, {2, 4, 96}, {2, 6}, {2, 6, 12}, {2, 6, 12, 24}, {2, 6, 12, 24, 48}, {2, 6, 12, 24, 48, 96}, {2, 6, 12, 24, 96}, {2, 6, 12, 48}, {2, 6, 12, 48, 96}, {2, 6, 12, 96}, {2, 6, 24}, {2, 6, 24, 48}, {2, 6, 24, 48, 96}, {2, 6, 24, 96}, {2, 6, 48}, {2, 6, 48, 96}, {2, 6, 96}, {2, 8}, {2, 8, 16}, {2, 8, 16, 32}, {2, 8, 16, 32, 96}, {2, 8, 16, 48}, {2, 8, 16, 48, 96}, {2, 8, 16, 96}, {2, 8, 24}, {2, 8, 24, 48}, {2, 8, 24, 48, 96}, {2, 8, 24, 96}, {2, 8, 32}, {2, 8, 32, 96}, {2, 8, 48}, {2, 8, 48, 96}, {2, 8, 96}, {2, 12}, {2, 12, 24}, {2, 12, 24, 48}, {2, 12, 24, 48, 96}, {2, 12, 24, 96}, {2, 12, 48}, {2, 12, 48, 96}, {2, 12, 96}, {2, 16}, {2, 16, 32}, {2, 16, 32, 96}, {2, 16, 48}, {2, 16, 48, 96}, {2, 16, 96}, {2, 24}, {2, 24, 48}, {2, 24, 48, 96}, {2, 24, 96}, {2, 32}, {2, 32, 96}, {2, 48}, {2, 48, 96}, {2, 96}, {3}, {3, 6}, {3, 6, 12}, {3, 6, 12, 24}, {3, 6, 12, 24, 48}, {3, 6, 12, 24, 48, 96}, {3, 6, 12, 24, 96}, {3, 6, 12, 48}, {3, 6, 12, 48, 96}, {3, 6, 12, 96}, {3, 6, 24}, {3, 6, 24, 48}, {3, 6, 24, 48, 96}, {3, 6, 24, 96}, {3, 6, 48}, {3, 6, 48, 96}, {3, 6, 96}, {3, 12}, {3, 12, 24}, {3, 12, 24, 48}, {3, 12, 24, 48, 96}, {3, 12, 24, 96}, {3, 12, 48}, {3, 12, 48, 96}, {3, 12, 96}, {3, 24}, {3, 24, 48}, {3, 24, 48, 96}, {3, 24, 96}, {3, 48}, {3, 48, 96}, {3, 96}, {4}, {4, 8}, {4, 8, 16}, {4, 8, 16, 32}, {4, 8, 16, 32, 96}, {4, 8, 16, 48}, {4, 8, 16, 48, 96}, {4, 8, 16, 96}, {4, 8, 24}, {4, 8, 24, 48}, {4, 8, 24, 48, 96}, {4, 8, 24, 96}, {4, 8, 32}, {4, 8, 32, 96}, {4, 8, 48}, {4, 8, 48, 96}, {4, 8, 96}, {4, 12}, {4, 12, 24}, {4, 12, 24, 48}, {4, 12, 24, 48, 96}, {4, 12, 24, 96}, {4, 12, 48}, {4, 12, 48, 96}, {4, 12, 96}, {4, 16}, {4, 16, 32}, {4, 16, 32, 96}, {4, 16, 48}, {4, 16, 48, 96}, {4, 16, 96}, {4, 24}, {4, 24, 48}, {4, 24, 48, 96}, {4, 24, 96}, {4, 32}, {4, 32, 96}, {4, 48}, {4, 48, 96}, {4, 96}, {6}, {6, 12}, {6, 12, 24}, {6, 12, 24, 48}, {6, 12, 24, 48, 96}, {6, 12, 24, 96}, {6, 12, 48}, {6, 12, 48, 96}, {6, 12, 96}, {6, 24}, {6, 24, 48}, {6, 24, 48, 96}, {6, 24, 96}, {6, 48}, {6, 48, 96}, {6, 96}, {8}, {8, 16}, {8, 16, 32}, {8, 16, 32, 96}, {8, 16, 48}, {8, 16, 48, 96}, {8, 16, 96}, {8, 24}, {8, 24, 48}, {8, 24, 48, 96}, {8, 24, 96}, {8, 32}, {8, 32, 96}, {8, 48}, {8, 48, 96}, {8, 96}, {12}, {12, 24}, {12, 24, 48}, {12, 24, 48, 96}, {12, 24, 96}, {12, 48}, {12, 48, 96}, {12, 96}, {16}, {16, 32}, {16, 32, 96}, {16, 48}, {16, 48, 96}, {16, 96}, {24}, {24, 48}, {24, 48, 96}, {24, 96}, {32}, {32, 96}, {48}, {48, 96}, {96}})
assert(flagChains(B,{1,2,3}) == {{2, 4, 8}, {2, 4, 12}, {2, 6, 12}, {3, 6, 12}})
assert(chains B == sort join({{}},flatten apply(subsets({0,1,2,3,4,5,6}), s-> flagChains(B,s))))
assert(isAntichain(B,{3,8})==true)
assert(isAntichain(B,{2,16})==false)
assert(# linearExtensions B == 132)
assert(toString characteristicPolynomial B === "q^6-2*q^5+q^4")
assert(toString flagfPolynomial B === "6*q_0*q_1*q_2*q_3*q_4*q_5*q_6+6*q_0*q_1*q_2*q_3*q_4*q_5+5*q_0*q_1*q_2*q_3*q_4*q_6+5*q_0*q_1*q_2*q_3*q_5*q_6+5*q_0*q_1*q_2*q_4*q_5*q_6+5*q_0*q_1*q_3*q_4*q_5*q_6+5*q_0*q_2*q_3*q_4*q_5*q_6+6*q_1*q_2*q_3*q_4*q_5*q_6+5*q_0*q_1*q_2*q_3*q_4+5*q_0*q_1*q_2*q_3*q_5+5*q_0*q_1*q_2*q_4*q_5+5*q_0*q_1*q_3*q_4*q_5+5*q_0*q_2*q_3*q_4*q_5+6*q_1*q_2*q_3*q_4*q_5+4*q_0*q_1*q_2*q_3*q_6+4*q_0*q_1*q_2*q_4*q_6+4*q_0*q_1*q_3*q_4*q_6+4*q_0*q_2*q_3*q_4*q_6+5*q_1*q_2*q_3*q_4*q_6+4*q_0*q_1*q_2*q_5*q_6+4*q_0*q_1*q_3*q_5*q_6+4*q_0*q_2*q_3*q_5*q_6+5*q_1*q_2*q_3*q_5*q_6+4*q_0*q_1*q_4*q_5*q_6+4*q_0*q_2*q_4*q_5*q_6+5*q_1*q_2*q_4*q_5*q_6+4*q_0*q_3*q_4*q_5*q_6+5*q_1*q_3*q_4*q_5*q_6+5*q_2*q_3*q_4*q_5*q_6+4*q_0*q_1*q_2*q_3+4*q_0*q_1*q_2*q_4+4*q_0*q_1*q_3*q_4+4*q_0*q_2*q_3*q_4+5*q_1*q_2*q_3*q_4+4*q_0*q_1*q_2*q_5+4*q_0*q_1*q_3*q_5+4*q_0*q_2*q_3*q_5+5*q_1*q_2*q_3*q_5+4*q_0*q_1*q_4*q_5+4*q_0*q_2*q_4*q_5+5*q_1*q_2*q_4*q_5+4*q_0*q_3*q_4*q_5+5*q_1*q_3*q_4*q_5+5*q_2*q_3*q_4*q_5+3*q_0*q_1*q_2*q_6+3*q_0*q_1*q_3*q_6+3*q_0*q_2*q_3*q_6+4*q_1*q_2*q_3*q_6+3*q_0*q_1*q_4*q_6+3*q_0*q_2*q_4*q_6+4*q_1*q_2*q_4*q_6+3*q_0*q_3*q_4*q_6+4*q_1*q_3*q_4*q_6+4*q_2*q_3*q_4*q_6+3*q_0*q_1*q_5*q_6+3*q_0*q_2*q_5*q_6+4*q_1*q_2*q_5*q_6+3*q_0*q_3*q_5*q_6+4*q_1*q_3*q_5*q_6+4*q_2*q_3*q_5*q_6+3*q_0*q_4*q_5*q_6+4*q_1*q_4*q_5*q_6+4*q_2*q_4*q_5*q_6+4*q_3*q_4*q_5*q_6+3*q_0*q_1*q_2+3*q_0*q_1*q_3+3*q_0*q_2*q_3+4*q_1*q_2*q_3+3*q_0*q_1*q_4+3*q_0*q_2*q_4+4*q_1*q_2*q_4+3*q_0*q_3*q_4+4*q_1*q_3*q_4+4*q_2*q_3*q_4+3*q_0*q_1*q_5+3*q_0*q_2*q_5+4*q_1*q_2*q_5+3*q_0*q_3*q_5+4*q_1*q_3*q_5+4*q_2*q_3*q_5+3*q_0*q_4*q_5+4*q_1*q_4*q_5+4*q_2*q_4*q_5+4*q_3*q_4*q_5+2*q_0*q_1*q_6+2*q_0*q_2*q_6+3*q_1*q_2*q_6+2*q_0*q_3*q_6+3*q_1*q_3*q_6+3*q_2*q_3*q_6+2*q_0*q_4*q_6+3*q_1*q_4*q_6+3*q_2*q_4*q_6+3*q_3*q_4*q_6+2*q_0*q_5*q_6+3*q_1*q_5*q_6+3*q_2*q_5*q_6+3*q_3*q_5*q_6+3*q_4*q_5*q_6+2*q_0*q_1+2*q_0*q_2+3*q_1*q_2+2*q_0*q_3+3*q_1*q_3+3*q_2*q_3+2*q_0*q_4+3*q_1*q_4+3*q_2*q_4+3*q_3*q_4+2*q_0*q_5+3*q_1*q_5+3*q_2*q_5+3*q_3*q_5+3*q_4*q_5+q_0*q_6+2*q_1*q_6+2*q_2*q_6+2*q_3*q_6+2*q_4*q_6+2*q_5*q_6+q_0+2*q_1+2*q_2+2*q_3+2*q_4+2*q_5+q_6+1")
--Removed for time purposes (slow!)
--assert(toString flaghPolynomial B === "q_1+q_2+q_3+q_4+q_5+1")
assert(toString fPolynomial B === "6*q^7+37*q^6+96*q^5+135*q^4+110*q^3+51*q^2+12*q+1")
assert(toString hPolynomial B === "5*q+1")
--Removed for time purposes (slow!)
--assert(greeneKleitmanPartition B === new Partition from {7,5})
assert(moebiusFunction B === new HashTable from {(1,6) => 1, (24,48) => -1, (48,24) => 0, (1,8) => 0, (1,12) => 0, (32,48) => 0, (48,32) => 0, (1,16) => 0, (1,24) => 0, (48,48) => 1, (1,32) => 0, (96,1) => 0, (96,2) => 0, (96,3) => 0, (4,96) => 0, (96,4) => 0, (96,6) => 0, (8,96) => 0, (96,8) => 0, (12,96) => 0, (96,12) => 0, (16,96) => 1, (96,16) => 0, (1,48) => 0, (24,96) => 0, (96,24) => 0, (96,32) => 0, (32,96) => -1, (2,1) => 0, (2,2) => 1, (2,3) => 0, (2,4) => -1, (6,1) => 0, (2,6) => -1, (6,2) => 0, (6,3) => 0, (2,8) => 0, (6,4) => 0, (6,6) => 1, (6,8) => 0, (2,12) => 1, (96,48) => 0, (48,96) => -1, (6,12) => -1, (2,16) => 0, (6,16) => 0, (2,24) => 0, (6,24) => 0, (1,96) => 0, (2,32) => 0, (6,32) => 0, (2,48) => 0, (6,48) => 0, (96,96) => 1, (3,1) => 0, (3,2) => 0, (3,3) => 1, (3,4) => 0, (3,6) => -1, (3,8) => 0, (3,12) => 0, (3,16) => 0, (3,24) => 0, (2,96) => 0, (3,32) => 0, (6,96) => 0, (3,48) => 0, (4,1) => 0, (4,2) => 0, (4,3) => 0, (4,4) => 1, (8,1) => 0, (8,2) => 0, (4,6) => 0, (8,3) => 0, (8,4) => 0, (4,8) => -1, (12,1) => 0, (12,2) => 0, (8,6) => 0, (12,3) => 0, (12,4) => 0, (8,8) => 1, (4,12) => -1, (16,1) => 0, (12,6) => 0, (16,2) => 0, (16,3) => 0, (12,8) => 0, (8,12) => 0, (16,4) => 0, (4,16) => 0, (16,6) => 0, (8,16) => -1, (12,12) => 1, (16,8) => 0, (24,1) => 0, (24,2) => 0, (24,3) => 0, (24,4) => 0, (12,16) => 0, (4,24) => 1, (16,12) => 0, (24,6) => 0, (24,8) => 0, (8,24) => -1, (16,16) => 1, (32,1) => 0, (32,2) => 0, (32,3) => 0, (3,96) => 0, (24,12) => 0, (32,4) => 0, (12,24) => -1, (4,32) => 0, (32,6) => 0, (24,16) => 0, (8,32) => 0, (32,8) => 0, (16,24) => 0, (32,12) => 0, (12,32) => 0, (24,24) => 1, (32,16) => 0, (16,32) => -1, (48,1) => 0, (48,2) => 0, (48,3) => 0, (48,4) => 0, (4,48) => 0, (48,6) => 0, (24,32) => 0, (32,24) => 0, (8,48) => 1, (48,8) => 0, (12,48) => 0, (48,12) => 0, (32,32) => 1, (48,16) => 0, (16,48) => -1, (1,1) => 1, (1,2) => -1, (1,3) => -1, (1,4) => 0})
assert(toString rankGeneratingFunction B === "q^6+2*q^5+2*q^4+2*q^3+2*q^2+2*q+1")
assert(toString zetaPolynomial B == "(1/120)*q^6+(1/12)*q^5+(7/24)*q^4+(5/12)*q^3+(1/5)*q^2")
assert(dilworthNumber B === 2)
assert(isAtomic B == false)
assert(isBounded B == true)
assert(isConnected B == true)
assert(isDistributive B == true)
assert(isEulerian B == false)
assert(isGeometric B == false)
assert(isGraded B == true)
assert(isLattice B == true)
assert(isLowerSemilattice B == true)
assert(isLowerSemimodular B == true)
assert(isModular B == true)
assert(isRanked B == true)
assert(isSperner B == true)
assert(isStrictSperner B == false)
assert(isUpperSemilattice B == true)
assert(isUpperSemimodular B == true)

///

--Tests for divisorPoset(Monomial)

TEST ///
R = QQ[x,y,z]
assert(divisorPoset(x*y*z)== booleanLattice 3)
B = divisorPoset(x^2*y*z)
assert(isLowerSemilattice B)
assert(isUpperSemilattice B)
assert(isDistributive B)
assert(hasseDiagram B === digraph {{0, 1}, {0, 2}, {0, 3}, {1, 4}, {1, 5}, {2, 4}, {2, 6}, {3, 5}, {3, 6}, {3, 7}, {4, 8}, {5, 8}, {5, 9}, {6, 8}, {6, 10}, {7, 9}, {7, 10}, {8, 11}, {9, 11}, {10, 11}})
assert(incomparabilityGraph B === graph({{1, 10}, {1, 2}, {1, 3}, {1, 6}, {1, 7}, {9, 2}, {2, 3}, {5, 2}, {2, 7}, {4, 3}, {4, 9}, {4, 10}, {4, 5}, {4, 6}, {4, 7}, {5, 6}, {5, 10}, {5, 7}, {9, 6}, {6, 7}, {8, 7}, {8, 9}, {8, 10}, {9, 10}}, Singletons =>{0,11}))
S=ring orderComplex B
assert(sub(ideal(flatten entries facets orderComplex B),R) == sub(ideal(v_0*v_3*v_7*v_10*v_11,v_0*v_3*v_6*v_10*v_11,v_0*v_2*v_6*v_10*v_11,v_0*v_3*v_7*v_9*v_11,v_0*v_3*v_5*v_9*v_11,v_0*v_1*v_5*v_9*v_11,v_0*v_3*v_6*v_8*v_11,v_0*v_2*v_6*v_8*v_11,v_0*v_3*v_5*v_8*v_11,v_0*v_1*v_5*v_8*v_11,v_0*v_2*v_4*v_8*v_11,v_0*v_1*v_4*v_8*v_11),R))
assert(sub(ideal(orderComplex B),S) == sub(ideal(v_1*v_2,v_1*v_3,v_2*v_3,v_3*v_4,v_2*v_5,v_4*v_5,v_1*v_6,v_4*v_6,v_5*v_6,v_1*v_7,v_2*v_7,v_4*v_7,v_5*v_7,v_6*v_7,v_7*v_8,v_2*v_9,v_4*v_9,v_6*v_9,v_8*v_9,v_1*v_10,v_4*v_10,v_5*v_10,v_8*v_10,v_9*v_10),S))
assert(closedInterval(B,y*z,x^2*y*z) == poset({{y*z, x*y*z}, {x*y*z, x^2*y*z}}))
assert(openInterval(B,sub(1,R),x^2*y*z) == poset({{z, x*z}, {z, y*z}, {y, x*y}, {y, y*z}, {x, x*z}, {x, x*y}, {x, x^2}, {y*z, x*y*z}, {x*z, x^2*z}, {x*z, x*y*z}, {x*y, x^2*y}, {x*y, x*y*z}, {x^2, x^2*z}, {x^2, x^2*y}}))
assert(dilworthLattice B == poset({{y*z, x*z, x*y, x^2}},{}))
D=distributiveLattice B;
assert(D.cache#OriginalPoset == B)

assert(# chains(D,1) == # D.GroundSet)
assert(# chains(D,2) == 837)
assert(hasseDiagram D === digraph new HashTable from {0 => set {1}, 1 => set {2, 3, 5}, 2 => set {4, 6}, 3 => set {4, 7}, 4 => set {8, 9}, 5 => set {6, 7, 19}, 6 => set {8, 11, 20}, 7 => set {8, 14, 21}, 8 => set {10, 12, 15, 22}, 9 => set {10}, 10 => set {13, 16, 23}, 11 => set {12, 24}, 12 => set {13, 17, 25}, 13 => set {18, 26}, 14 => set {15, 27}, 15 => set {16, 17, 28}, 16 => set {18, 29}, 17 => set {18, 30}, 18 => set {31, 32}, 19 => set {20, 21}, 20 => set {22, 24}, 21 => set {22, 27}, 22 => set {23, 25, 28}, 23 => set {26, 29}, 24 => set {25, 34}, 25 => set {26, 30, 35}, 26 => set {31, 36}, 27 => set {28, 40}, 28 => set {29, 30, 41}, 29 => set {31, 42}, 30 => set {31, 37, 43}, 31 => set {33, 38, 44}, 32 => set {33}, 33 => set {39, 45}, 34 => set {35}, 35 => set {36, 37}, 36 => set {38}, 37 => set {38, 46}, 38 => set {39, 47}, 39 => set {48}, 40 => set {41}, 41 => set {42, 43}, 42 => set {44}, 43 => set {44, 46}, 44 => set {45, 47}, 45 => set {48}, 46 => set {47}, 47 => set {48}, 48 => set {49}, 49 => set {}})
assert(sort filter(B, {x*y,x^2}) == {x*y, x^2, x*y*z, x^2*z, x^2*y, x^2*y*z})
assert(sort orderIdeal(B,{x*y,x^2}) == {1, y, x, x*y, x^2})
assert(sort principalFilter(B,x^2) == {x^2, x^2*z, x^2*y, x^2*y*z})
assert(sort principalOrderIdeal(B,x^2*y) == {1, y, x, x*y, x^2, x^2*y})
assert(subposet(B, filter(B,{x*y,x^2})) == poset {{x*y, x^2*y}, {x*y, x*y*z}, {x^2, x^2*y}, {x^2, x^2*z}, {x*y*z, x^2*y*z}, {x^2*z, x^2*y*z}, {x^2*y, x^2*y*z}})
assert(subposet(B, orderIdeal(B, {x*y,x^2})) == poset {{1, y}, {1, x}, {y, x*y}, {x, x^2}, {x, x*y}})
assert(subposet(B,principalFilter(B,x*y)) == poset {{x*y, x*y*z}, {x*y, x^2*y}, {x*y*z, x^2*y*z}, {x^2*y, x^2*y*z}})
assert(subposet(B,principalOrderIdeal(B,x^2*y)) == poset {{1, y}, {1, x}, {y, x*y}, {x, x^2}, {x, x*y}, {x*y, x^2*y}, {x^2, x^2*y}})
assert(sort rankFunction B == {0, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 4})
assert(flagPoset(B,{1,3}) == poset {{z, x^2*z}, {z, x*y*z}, {y, x^2*y}, {y, x*y*z}, {x, x^2*z}, {x, x^2*y}, {x, x*y*z}})
assert(flagPoset(B,{1,2,3}) == subposet(B,{z, y, x, y*z, x*z, x*y, x^2, x*y*z, x^2*z, x^2*y}))
assert(flagPoset(B,{1,3}) == dropElements(B,{sub(1,ring first B.GroundSet), sub(y*z,ring first B.GroundSet), sub(x*z,ring first B.GroundSet), sub(x*y,ring first B.GroundSet), sub(x^2,ring first B.GroundSet), sub(x^2*y*z,ring first B.GroundSet)}))
assert(flagPoset(B,{1,2,3}) == dropElements(B,{sub(1,ring first B.GroundSet), sub(x^2*y*z,ring first B.GroundSet)}))
assert(B == indexLabeling B)
assert(B == naturalLabeling B)
r = flatten apply(rankPoset naturalLabeling B, sort)
assert(r == toList(0..#r-1))
assert(adjoinMin(flagPoset(B,{1,2,3,4})) == B)
assert(adjoinMax(flagPoset(B,{0,1,2,3})) == B)
assert(augmentPoset(flagPoset(B,{1,2,3})) == B)
--Removed for time purposes (slow!)

--Stopped here for the night.
assert(hasseDiagram(diamondProduct(B,B))===digraph new HashTable from {0 => set {1, 2, 12, 13}, 1 => set {3, 4, 23, 34}, 2 => set {4, 24, 35}, 3 => set {5, 6, 25, 36}, 4 => set {6, 26, 37}, 5 => set {7, 8, 27, 38}, 6 => set {8, 28, 39}, 7 => set{9, 10, 29, 40}, 8 => set {10, 30, 41}, 9 => set {11, 31, 42}, 10 => set {11, 32, 43}, 11 => set {33, 44}, 12 => set {14, 15, 34}, 13 => set {15, 35}, 14 => set {16, 17, 36}, 15 => set {17, 37}, 16 => set {18, 19, 38}, 17 => set {19, 39}, 18 => set {20, 21, 40}, 19 => set {21, 41}, 20 => set {22, 42}, 21 => set {22, 43}, 22 => set {44}, 23 => set {25, 26, 45, 56}, 24 => set {26, 46, 57}, 25 => set {27, 28, 47, 58}, 26 => set {28, 48, 59}, 27 => set {29, 30, 49, 60}, 28 => set {30, 50, 61}, 29 => set {31, 32, 51, 62}, 30 => set {32, 52, 63}, 31 => set {33, 53, 64}, 32 => set {33, 54, 65}, 33 => set {55, 66}, 34 => set {36, 37, 56}, 35 => set {37, 57}, 36 => set {38, 39, 58}, 37 => set {39, 59}, 38 => set {40, 41, 60}, 39 => set {41, 61}, 40 => set {42, 43, 62}, 41 => set {43, 63}, 42 => set {44, 64}, 43 => set {44, 65}, 44 => set {66}, 45 => set {47, 48, 67, 78}, 46 => set {48, 68, 79}, 47 => set {49, 50, 69, 80}, 48 => set {50, 70, 81}, 49 => set {51, 52, 71, 82}, 50 => set {52, 72, 83}, 51 => set {53, 54, 73, 84}, 52 => set {54, 74, 85}, 53 => set {55, 75, 86}, 54 => set {55, 76, 87}, 55 => set {77, 88}, 56 => set {58, 59, 78}, 57 => set {59, 79}, 58 => set {60, 61, 80}, 59 => set {61, 81}, 60 => set {62, 63, 82}, 61 => set {63, 83}, 62 => set {64, 65, 84}, 63 => set {65, 85}, 64 => set {66, 86}, 65 => set {66, 87}, 66 => set {88}, 67 => set {69, 70, 89, 100}, 68 => set {70, 90, 101}, 69 => set {71, 72, 91, 102}, 70 => set {72, 92, 103}, 71 => set {73, 74, 93, 104}, 72 => set {74, 94, 105}, 73 => set {75, 76, 95, 106}, 74 => set {76, 96, 107}, 75 => set {77, 97, 108}, 76 => set {77, 98, 109}, 77 => set {99, 110}, 78 => set {80, 81, 100}, 79 => set {81, 101}, 80 => set {82, 83, 102}, 81 => set {83, 103}, 82 => set {84, 85, 104}, 83 => set {85, 105}, 84 => set {86, 87, 106}, 85 => set {87, 107}, 86 => set {88, 108}, 87 => set {88, 109}, 88 => set {110}, 89 => set {91, 92, 111}, 90 => set {92, 112}, 91 => set {93, 94, 113}, 92 => set {94, 114}, 93 => set {95, 96, 115}, 94 => set {96, 116}, 95 => set {97, 98, 117}, 96 => set {98, 118}, 97 => set {99, 119}, 98 => set {99, 120}, 99 => set {121}, 100 => set {102, 103, 111}, 101 => set {103, 112}, 102 => set {104, 105, 113}, 103 => set {105, 114}, 104 => set {106, 107, 115}, 105 => set {107, 116}, 106 => set {108, 109, 117}, 107 => set {109, 118}, 108 => set {110, 119}, 109 => set {110, 120}, 110 => set {121}, 111 => set {113, 114}, 112 => set {114}, 113 => set {115, 116}, 114 => set {116}, 115 => set {117, 118}, 116 => set {118}, 117 => set {119, 120}, 118 => set {120}, 119 => set {121}, 120 => set {121}, 121 => set {}})
assert(union(B,B)==B)
assert(atoms B == {2,3})
assert(compare(B,3,4) == false)
assert(compare(B,3,6) == true)
assert(compare(B,3,48) == true)
assert((sort \ (filtration B)) == (sort \ (rankPoset B)))
assert(joinExists(B,2,3) == true)
assert(joinExists(B,3,6) == true)
assert(joinExists(B,3,8) == true)
assert(sort joinIrreducibles B == {1, 2, 3, 4, 8, 16, 32})
assert(meetExists(B,16,3) == true)
assert(meetExists(B,32,24) == true)
assert(meetExists(B,32,16) == true)
assert(sort meetIrreducibles B == {3, 6, 12, 24, 32, 48, 96})
assert(maximalElements B == {96})
assert(minimalElements B == {1})
assert(posetJoin(B,2,3)== {6})
assert(posetJoin(B,3,6)== {6})
assert(posetJoin(B,3,8)== {24})
assert(posetMeet(B,16,3)== {1})
assert(posetMeet(B,32,24)== {gcd(24,32)})
assert(posetMeet(B,32,16)== {16})
assert(rankPoset B == {{1}, {2, 3}, {4, 6}, {8, 12}, {16, 24}, {32, 48}, {96}})
assert(allRelations B == {{1, 1}, {1, 2}, {1, 3}, {1, 4}, {1, 6}, {1, 8}, {1, 12}, {1,16}, {1, 24}, {1, 32}, {1, 48}, {1, 96}, {2, 2}, {2, 4}, {2, 6}, {2, 8}, {2, 12}, {2, 16}, {2, 24}, {2, 32}, {2, 48}, {2, 96}, {3, 3}, {3, 6}, {3, 12}, {3, 24}, {3, 48}, {3, 96}, {4, 4}, {4, 8}, {4, 12}, {4, 16}, {4, 24}, {4, 32}, {4, 48}, {4, 96}, {6, 6}, {6, 12}, {6, 24}, {6, 48}, {6, 96}, {8, 8}, {8, 16}, {8, 24}, {8,32}, {8, 48}, {8, 96}, {12, 12}, {12, 24}, {12, 48}, {12, 96}, {16, 16}, {16, 32}, {16, 48}, {16, 96}, {24, 24}, {24, 48}, {24, 96}, {32, 32}, {32, 96}, {48, 48}, {48, 96}, {96, 96}})
assert(coveringRelations B == {{1, 2}, {1, 3}, {2, 6}, {2, 4}, {3, 6}, {4, 8}, {4, 12}, {6, 12}, {8, 24}, {8, 16}, {12, 24}, {16, 32}, {16, 48}, {24, 48}, {32, 96}, {48, 96}})
assert(antichains B == {{}, {1}, {2}, {2, 3}, {3}, {3, 4}, {3, 8}, {3, 16}, {3, 32}, {4}, {4, 6}, {6}, {6, 8}, {6, 16}, {6, 32}, {8}, {8, 12}, {12}, {12, 16}, {12, 32}, {16}, {16, 24}, {24}, {24, 32}, {32}, {32, 48}, {48}, {96}})
assert(maximalAntichains B == {{1}, {96}, {2, 3}, {3, 32}, {3, 4}, {3, 8}, {3, 16}, {4, 6}, {6, 32}, {6, 8}, {6, 16}, {8, 12}, {12, 32}, {12, 16}, {16, 24}, {24, 32}, {32, 48}})
assert(maximalChains B == {{1, 2, 6, 12, 24, 48, 96}, {1, 2, 4, 8, 24, 48, 96}, {1, 2, 4, 8, 16, 32, 96}, {1, 2, 4, 8, 16, 48, 96}, {1, 2, 4, 12, 24, 48, 96}, {1, 3, 6, 12, 24, 48, 96}})
assert(chains B == {{}, {1}, {1, 2}, {1, 2, 4}, {1, 2, 4, 8}, {1, 2, 4, 8, 16}, {1, 2, 4, 8, 16, 32}, {1, 2, 4, 8, 16, 32, 96}, {1, 2, 4, 8, 16, 48}, {1, 2, 4, 8, 16, 48, 96}, {1, 2, 4, 8, 16, 96}, {1, 2, 4, 8, 24}, {1, 2, 4, 8, 24, 48}, {1, 2, 4, 8, 24, 48, 96}, {1, 2, 4, 8, 24, 96}, {1, 2, 4, 8, 32}, {1, 2, 4, 8, 32, 96}, {1, 2, 4, 8, 48}, {1, 2, 4, 8, 48, 96}, {1, 2, 4, 8, 96}, {1, 2, 4, 12}, {1, 2, 4, 12, 24}, {1, 2, 4, 12, 24, 48}, {1, 2, 4, 12, 24, 48, 96}, {1, 2, 4, 12, 24, 96}, {1, 2, 4, 12, 48}, {1, 2, 4, 12, 48, 96}, {1, 2, 4, 12, 96}, {1, 2, 4, 16}, {1, 2, 4, 16, 32}, {1, 2, 4, 16, 32, 96}, {1, 2, 4, 16, 48}, {1, 2, 4, 16, 48, 96}, {1, 2, 4, 16, 96}, {1, 2, 4, 24}, {1, 2, 4, 24, 48}, {1, 2, 4, 24, 48, 96}, {1, 2, 4, 24, 96}, {1, 2, 4, 32}, {1, 2, 4, 32, 96}, {1, 2, 4, 48}, {1, 2, 4, 48, 96}, {1, 2, 4, 96}, {1, 2, 6}, {1, 2, 6, 12}, {1, 2, 6, 12, 24}, {1, 2, 6, 12, 24, 48}, {1, 2, 6, 12, 24, 48, 96}, {1, 2, 6, 12, 24, 96}, {1, 2, 6, 12, 48}, {1, 2, 6, 12, 48, 96}, {1, 2, 6, 12, 96}, {1, 2, 6, 24}, {1, 2, 6, 24, 48}, {1, 2, 6, 24, 48, 96}, {1, 2, 6, 24, 96}, {1, 2, 6, 48}, {1, 2, 6, 48, 96}, {1, 2, 6, 96}, {1, 2, 8}, {1, 2, 8, 16}, {1, 2, 8, 16, 32}, {1, 2, 8, 16, 32, 96}, {1, 2, 8, 16, 48}, {1, 2, 8, 16, 48, 96}, {1, 2, 8, 16, 96}, {1, 2, 8, 24}, {1, 2, 8, 24, 48}, {1, 2, 8, 24, 48, 96}, {1, 2, 8, 24, 96}, {1, 2, 8, 32}, {1, 2, 8, 32, 96}, {1, 2, 8, 48}, {1, 2, 8, 48, 96}, {1, 2, 8, 96}, {1, 2, 12}, {1, 2, 12, 24}, {1, 2, 12, 24, 48}, {1, 2, 12, 24, 48, 96}, {1, 2, 12, 24, 96}, {1, 2, 12, 48}, {1, 2, 12, 48, 96}, {1, 2, 12, 96}, {1, 2, 16}, {1, 2, 16, 32}, {1, 2, 16, 32, 96}, {1, 2, 16, 48}, {1, 2, 16, 48, 96}, {1, 2, 16, 96}, {1, 2, 24}, {1, 2, 24, 48}, {1, 2, 24, 48, 96}, {1, 2, 24, 96}, {1, 2, 32}, {1, 2, 32, 96}, {1, 2, 48}, {1, 2, 48, 96}, {1, 2, 96}, {1, 3}, {1, 3, 6}, {1, 3, 6, 12}, {1, 3, 6, 12, 24}, {1, 3, 6, 12, 24, 48}, {1, 3, 6, 12, 24, 48, 96}, {1, 3, 6, 12, 24, 96}, {1, 3, 6, 12, 48}, {1, 3, 6, 12, 48, 96}, {1, 3, 6, 12, 96}, {1, 3, 6, 24}, {1, 3, 6, 24, 48}, {1, 3, 6, 24, 48, 96}, {1, 3, 6, 24, 96}, {1, 3, 6, 48}, {1, 3, 6, 48, 96}, {1, 3, 6, 96}, {1, 3, 12}, {1, 3, 12, 24}, {1, 3, 12, 24, 48}, {1, 3, 12, 24, 48, 96}, {1, 3, 12, 24, 96}, {1, 3, 12, 48}, {1, 3, 12, 48, 96}, {1, 3, 12, 96}, {1, 3, 24}, {1, 3, 24, 48}, {1, 3, 24, 48, 96}, {1, 3, 24, 96}, {1, 3, 48}, {1, 3, 48, 96}, {1, 3, 96}, {1, 4}, {1, 4, 8}, {1, 4, 8, 16}, {1, 4, 8, 16, 32}, {1, 4, 8, 16, 32, 96}, {1, 4, 8, 16, 48}, {1, 4, 8, 16, 48, 96}, {1, 4, 8, 16, 96}, {1, 4, 8, 24}, {1, 4, 8, 24, 48}, {1, 4, 8, 24, 48, 96}, {1, 4, 8, 24, 96}, {1, 4, 8, 32}, {1, 4, 8, 32, 96}, {1, 4, 8, 48}, {1, 4, 8, 48, 96}, {1, 4, 8, 96}, {1, 4, 12}, {1, 4, 12, 24}, {1, 4, 12, 24, 48}, {1, 4, 12, 24, 48, 96}, {1, 4, 12, 24, 96}, {1, 4, 12, 48}, {1, 4, 12, 48, 96}, {1, 4, 12, 96}, {1, 4, 16}, {1, 4, 16, 32}, {1, 4, 16, 32, 96}, {1, 4, 16, 48}, {1, 4, 16, 48, 96}, {1, 4, 16, 96}, {1, 4, 24}, {1, 4, 24, 48}, {1, 4, 24, 48, 96}, {1, 4, 24, 96}, {1, 4, 32}, {1, 4, 32, 96}, {1, 4, 48}, {1, 4, 48, 96}, {1, 4, 96}, {1, 6}, {1, 6, 12}, {1, 6, 12, 24}, {1, 6, 12, 24, 48}, {1, 6, 12, 24, 48, 96}, {1, 6, 12, 24, 96}, {1, 6, 12, 48}, {1, 6, 12, 48, 96}, {1, 6, 12, 96}, {1, 6, 24}, {1, 6, 24, 48}, {1, 6, 24, 48, 96}, {1, 6, 24, 96}, {1, 6, 48}, {1, 6, 48, 96}, {1, 6, 96}, {1, 8}, {1, 8, 16}, {1, 8, 16, 32}, {1, 8, 16, 32, 96}, {1, 8, 16, 48}, {1, 8, 16, 48, 96}, {1, 8, 16, 96}, {1, 8, 24}, {1, 8, 24, 48}, {1, 8, 24, 48, 96}, {1, 8, 24, 96}, {1, 8, 32}, {1, 8, 32, 96}, {1, 8, 48}, {1, 8, 48, 96}, {1, 8, 96}, {1, 12}, {1, 12, 24}, {1, 12, 24, 48}, {1, 12, 24, 48, 96}, {1, 12, 24, 96}, {1, 12, 48}, {1, 12, 48, 96}, {1, 12, 96}, {1, 16}, {1, 16, 32}, {1, 16, 32, 96}, {1, 16, 48}, {1, 16, 48, 96}, {1, 16, 96}, {1, 24}, {1, 24, 48}, {1, 24, 48, 96}, {1, 24, 96}, {1, 32}, {1, 32, 96}, {1, 48}, {1, 48, 96}, {1, 96}, {2}, {2, 4}, {2, 4, 8}, {2, 4, 8, 16}, {2, 4, 8, 16, 32}, {2, 4, 8, 16, 32, 96}, {2, 4, 8, 16, 48}, {2, 4, 8, 16, 48, 96}, {2, 4, 8, 16, 96}, {2, 4, 8, 24}, {2, 4, 8, 24, 48}, {2, 4, 8, 24, 48, 96}, {2, 4, 8, 24, 96}, {2, 4, 8, 32}, {2, 4, 8, 32, 96}, {2, 4, 8, 48}, {2, 4, 8, 48, 96}, {2, 4, 8, 96}, {2, 4, 12}, {2, 4, 12, 24}, {2, 4, 12, 24, 48}, {2, 4, 12, 24, 48, 96}, {2, 4, 12, 24, 96}, {2, 4, 12, 48}, {2, 4, 12, 48, 96}, {2, 4, 12, 96}, {2, 4, 16}, {2, 4, 16, 32}, {2, 4, 16, 32, 96}, {2, 4, 16, 48}, {2, 4, 16, 48, 96}, {2, 4, 16, 96}, {2, 4, 24}, {2, 4, 24, 48}, {2, 4, 24, 48, 96}, {2, 4, 24, 96}, {2, 4, 32}, {2, 4, 32, 96}, {2, 4, 48}, {2, 4, 48, 96}, {2, 4, 96}, {2, 6}, {2, 6, 12}, {2, 6, 12, 24}, {2, 6, 12, 24, 48}, {2, 6, 12, 24, 48, 96}, {2, 6, 12, 24, 96}, {2, 6, 12, 48}, {2, 6, 12, 48, 96}, {2, 6, 12, 96}, {2, 6, 24}, {2, 6, 24, 48}, {2, 6, 24, 48, 96}, {2, 6, 24, 96}, {2, 6, 48}, {2, 6, 48, 96}, {2, 6, 96}, {2, 8}, {2, 8, 16}, {2, 8, 16, 32}, {2, 8, 16, 32, 96}, {2, 8, 16, 48}, {2, 8, 16, 48, 96}, {2, 8, 16, 96}, {2, 8, 24}, {2, 8, 24, 48}, {2, 8, 24, 48, 96}, {2, 8, 24, 96}, {2, 8, 32}, {2, 8, 32, 96}, {2, 8, 48}, {2, 8, 48, 96}, {2, 8, 96}, {2, 12}, {2, 12, 24}, {2, 12, 24, 48}, {2, 12, 24, 48, 96}, {2, 12, 24, 96}, {2, 12, 48}, {2, 12, 48, 96}, {2, 12, 96}, {2, 16}, {2, 16, 32}, {2, 16, 32, 96}, {2, 16, 48}, {2, 16, 48, 96}, {2, 16, 96}, {2, 24}, {2, 24, 48}, {2, 24, 48, 96}, {2, 24, 96}, {2, 32}, {2, 32, 96}, {2, 48}, {2, 48, 96}, {2, 96}, {3}, {3, 6}, {3, 6, 12}, {3, 6, 12, 24}, {3, 6, 12, 24, 48}, {3, 6, 12, 24, 48, 96}, {3, 6, 12, 24, 96}, {3, 6, 12, 48}, {3, 6, 12, 48, 96}, {3, 6, 12, 96}, {3, 6, 24}, {3, 6, 24, 48}, {3, 6, 24, 48, 96}, {3, 6, 24, 96}, {3, 6, 48}, {3, 6, 48, 96}, {3, 6, 96}, {3, 12}, {3, 12, 24}, {3, 12, 24, 48}, {3, 12, 24, 48, 96}, {3, 12, 24, 96}, {3, 12, 48}, {3, 12, 48, 96}, {3, 12, 96}, {3, 24}, {3, 24, 48}, {3, 24, 48, 96}, {3, 24, 96}, {3, 48}, {3, 48, 96}, {3, 96}, {4}, {4, 8}, {4, 8, 16}, {4, 8, 16, 32}, {4, 8, 16, 32, 96}, {4, 8, 16, 48}, {4, 8, 16, 48, 96}, {4, 8, 16, 96}, {4, 8, 24}, {4, 8, 24, 48}, {4, 8, 24, 48, 96}, {4, 8, 24, 96}, {4, 8, 32}, {4, 8, 32, 96}, {4, 8, 48}, {4, 8, 48, 96}, {4, 8, 96}, {4, 12}, {4, 12, 24}, {4, 12, 24, 48}, {4, 12, 24, 48, 96}, {4, 12, 24, 96}, {4, 12, 48}, {4, 12, 48, 96}, {4, 12, 96}, {4, 16}, {4, 16, 32}, {4, 16, 32, 96}, {4, 16, 48}, {4, 16, 48, 96}, {4, 16, 96}, {4, 24}, {4, 24, 48}, {4, 24, 48, 96}, {4, 24, 96}, {4, 32}, {4, 32, 96}, {4, 48}, {4, 48, 96}, {4, 96}, {6}, {6, 12}, {6, 12, 24}, {6, 12, 24, 48}, {6, 12, 24, 48, 96}, {6, 12, 24, 96}, {6, 12, 48}, {6, 12, 48, 96}, {6, 12, 96}, {6, 24}, {6, 24, 48}, {6, 24, 48, 96}, {6, 24, 96}, {6, 48}, {6, 48, 96}, {6, 96}, {8}, {8, 16}, {8, 16, 32}, {8, 16, 32, 96}, {8, 16, 48}, {8, 16, 48, 96}, {8, 16, 96}, {8, 24}, {8, 24, 48}, {8, 24, 48, 96}, {8, 24, 96}, {8, 32}, {8, 32, 96}, {8, 48}, {8, 48, 96}, {8, 96}, {12}, {12, 24}, {12, 24, 48}, {12, 24, 48, 96}, {12, 24, 96}, {12, 48}, {12, 48, 96}, {12, 96}, {16}, {16, 32}, {16, 32, 96}, {16, 48}, {16, 48, 96}, {16, 96}, {24}, {24, 48}, {24, 48, 96}, {24, 96}, {32}, {32, 96}, {48}, {48, 96}, {96}})
assert(flagChains(B,{1,2,3}) == {{2, 4, 8}, {2, 4, 12}, {2, 6, 12}, {3, 6, 12}})
assert(chains B == sort join({{}},flatten apply(subsets({0,1,2,3,4,5,6}), s-> flagChains(B,s))))
assert(isAntichain(B,{3,8})==true)
assert(isAntichain(B,{2,16})==false)
assert(# linearExtensions B == 132)
assert(toString characteristicPolynomial B === "q^6-2*q^5+q^4")
assert(toString flagfPolynomial B === "6*q_0*q_1*q_2*q_3*q_4*q_5*q_6+6*q_0*q_1*q_2*q_3*q_4*q_5+5*q_0*q_1*q_2*q_3*q_4*q_6+5*q_0*q_1*q_2*q_3*q_5*q_6+5*q_0*q_1*q_2*q_4*q_5*q_6+5*q_0*q_1*q_3*q_4*q_5*q_6+5*q_0*q_2*q_3*q_4*q_5*q_6+6*q_1*q_2*q_3*q_4*q_5*q_6+5*q_0*q_1*q_2*q_3*q_4+5*q_0*q_1*q_2*q_3*q_5+5*q_0*q_1*q_2*q_4*q_5+5*q_0*q_1*q_3*q_4*q_5+5*q_0*q_2*q_3*q_4*q_5+6*q_1*q_2*q_3*q_4*q_5+4*q_0*q_1*q_2*q_3*q_6+4*q_0*q_1*q_2*q_4*q_6+4*q_0*q_1*q_3*q_4*q_6+4*q_0*q_2*q_3*q_4*q_6+5*q_1*q_2*q_3*q_4*q_6+4*q_0*q_1*q_2*q_5*q_6+4*q_0*q_1*q_3*q_5*q_6+4*q_0*q_2*q_3*q_5*q_6+5*q_1*q_2*q_3*q_5*q_6+4*q_0*q_1*q_4*q_5*q_6+4*q_0*q_2*q_4*q_5*q_6+5*q_1*q_2*q_4*q_5*q_6+4*q_0*q_3*q_4*q_5*q_6+5*q_1*q_3*q_4*q_5*q_6+5*q_2*q_3*q_4*q_5*q_6+4*q_0*q_1*q_2*q_3+4*q_0*q_1*q_2*q_4+4*q_0*q_1*q_3*q_4+4*q_0*q_2*q_3*q_4+5*q_1*q_2*q_3*q_4+4*q_0*q_1*q_2*q_5+4*q_0*q_1*q_3*q_5+4*q_0*q_2*q_3*q_5+5*q_1*q_2*q_3*q_5+4*q_0*q_1*q_4*q_5+4*q_0*q_2*q_4*q_5+5*q_1*q_2*q_4*q_5+4*q_0*q_3*q_4*q_5+5*q_1*q_3*q_4*q_5+5*q_2*q_3*q_4*q_5+3*q_0*q_1*q_2*q_6+3*q_0*q_1*q_3*q_6+3*q_0*q_2*q_3*q_6+4*q_1*q_2*q_3*q_6+3*q_0*q_1*q_4*q_6+3*q_0*q_2*q_4*q_6+4*q_1*q_2*q_4*q_6+3*q_0*q_3*q_4*q_6+4*q_1*q_3*q_4*q_6+4*q_2*q_3*q_4*q_6+3*q_0*q_1*q_5*q_6+3*q_0*q_2*q_5*q_6+4*q_1*q_2*q_5*q_6+3*q_0*q_3*q_5*q_6+4*q_1*q_3*q_5*q_6+4*q_2*q_3*q_5*q_6+3*q_0*q_4*q_5*q_6+4*q_1*q_4*q_5*q_6+4*q_2*q_4*q_5*q_6+4*q_3*q_4*q_5*q_6+3*q_0*q_1*q_2+3*q_0*q_1*q_3+3*q_0*q_2*q_3+4*q_1*q_2*q_3+3*q_0*q_1*q_4+3*q_0*q_2*q_4+4*q_1*q_2*q_4+3*q_0*q_3*q_4+4*q_1*q_3*q_4+4*q_2*q_3*q_4+3*q_0*q_1*q_5+3*q_0*q_2*q_5+4*q_1*q_2*q_5+3*q_0*q_3*q_5+4*q_1*q_3*q_5+4*q_2*q_3*q_5+3*q_0*q_4*q_5+4*q_1*q_4*q_5+4*q_2*q_4*q_5+4*q_3*q_4*q_5+2*q_0*q_1*q_6+2*q_0*q_2*q_6+3*q_1*q_2*q_6+2*q_0*q_3*q_6+3*q_1*q_3*q_6+3*q_2*q_3*q_6+2*q_0*q_4*q_6+3*q_1*q_4*q_6+3*q_2*q_4*q_6+3*q_3*q_4*q_6+2*q_0*q_5*q_6+3*q_1*q_5*q_6+3*q_2*q_5*q_6+3*q_3*q_5*q_6+3*q_4*q_5*q_6+2*q_0*q_1+2*q_0*q_2+3*q_1*q_2+2*q_0*q_3+3*q_1*q_3+3*q_2*q_3+2*q_0*q_4+3*q_1*q_4+3*q_2*q_4+3*q_3*q_4+2*q_0*q_5+3*q_1*q_5+3*q_2*q_5+3*q_3*q_5+3*q_4*q_5+q_0*q_6+2*q_1*q_6+2*q_2*q_6+2*q_3*q_6+2*q_4*q_6+2*q_5*q_6+q_0+2*q_1+2*q_2+2*q_3+2*q_4+2*q_5+q_6+1")
--Removed for time purposes (slow!)
--assert(toString flaghPolynomial B === "q_1+q_2+q_3+q_4+q_5+1")
assert(toString fPolynomial B === "6*q^7+37*q^6+96*q^5+135*q^4+110*q^3+51*q^2+12*q+1")
assert(toString hPolynomial B === "5*q+1")
--Removed for time purposes (slow!)
--assert(greeneKleitmanPartition B === new Partition from {7,5})
assert(moebiusFunction B === new HashTable from {(1,6) => 1, (24,48) => -1, (48,24) => 0, (1,8) => 0, (1,12) => 0, (32,48) => 0, (48,32) => 0, (1,16) => 0, (1,24) => 0, (48,48) => 1, (1,32) => 0, (96,1) => 0, (96,2) => 0, (96,3) => 0, (4,96) => 0, (96,4) => 0, (96,6) => 0, (8,96) => 0, (96,8) => 0, (12,96) => 0, (96,12) => 0, (16,96) => 1, (96,16) => 0, (1,48) => 0, (24,96) => 0, (96,24) => 0, (96,32) => 0, (32,96) => -1, (2,1) => 0, (2,2) => 1, (2,3) => 0, (2,4) => -1, (6,1) => 0, (2,6) => -1, (6,2) => 0, (6,3) => 0, (2,8) => 0, (6,4) => 0, (6,6) => 1, (6,8) => 0, (2,12) => 1, (96,48) => 0, (48,96) => -1, (6,12) => -1, (2,16) => 0, (6,16) => 0, (2,24) => 0, (6,24) => 0, (1,96) => 0, (2,32) => 0, (6,32) => 0, (2,48) => 0, (6,48) => 0, (96,96) => 1, (3,1) => 0, (3,2) => 0, (3,3) => 1, (3,4) => 0, (3,6) => -1, (3,8) => 0, (3,12) => 0, (3,16) => 0, (3,24) => 0, (2,96) => 0, (3,32) => 0, (6,96) => 0, (3,48) => 0, (4,1) => 0, (4,2) => 0, (4,3) => 0, (4,4) => 1, (8,1) => 0, (8,2) => 0, (4,6) => 0, (8,3) => 0, (8,4) => 0, (4,8) => -1, (12,1) => 0, (12,2) => 0, (8,6) => 0, (12,3) => 0, (12,4) => 0, (8,8) => 1, (4,12) => -1, (16,1) => 0, (12,6) => 0, (16,2) => 0, (16,3) => 0, (12,8) => 0, (8,12) => 0, (16,4) => 0, (4,16) => 0, (16,6) => 0, (8,16) => -1, (12,12) => 1, (16,8) => 0, (24,1) => 0, (24,2) => 0, (24,3) => 0, (24,4) => 0, (12,16) => 0, (4,24) => 1, (16,12) => 0, (24,6) => 0, (24,8) => 0, (8,24) => -1, (16,16) => 1, (32,1) => 0, (32,2) => 0, (32,3) => 0, (3,96) => 0, (24,12) => 0, (32,4) => 0, (12,24) => -1, (4,32) => 0, (32,6) => 0, (24,16) => 0, (8,32) => 0, (32,8) => 0, (16,24) => 0, (32,12) => 0, (12,32) => 0, (24,24) => 1, (32,16) => 0, (16,32) => -1, (48,1) => 0, (48,2) => 0, (48,3) => 0, (48,4) => 0, (4,48) => 0, (48,6) => 0, (24,32) => 0, (32,24) => 0, (8,48) => 1, (48,8) => 0, (12,48) => 0, (48,12) => 0, (32,32) => 1, (48,16) => 0, (16,48) => -1, (1,1) => 1, (1,2) => -1, (1,3) => -1, (1,4) => 0})
assert(toString rankGeneratingFunction B === "q^6+2*q^5+2*q^4+2*q^3+2*q^2+2*q+1")
assert(toString zetaPolynomial B == "(1/120)*q^6+(1/12)*q^5+(7/24)*q^4+(5/12)*q^3+(1/5)*q^2")
assert(dilworthNumber B === 2)
assert(isAtomic B == false)
assert(isBounded B == true)
assert(isConnected B == true)
assert(isDistributive B == true)
assert(isEulerian B == false)
assert(isGeometric B == false)
assert(isGraded B == true)
assert(isLattice B == true)
assert(isLowerSemilattice B == true)
assert(isLowerSemimodular B == true)
assert(isModular B == true)
assert(isRanked B == true)
assert(isSperner B == true)
assert(isStrictSperner B == false)
assert(isUpperSemilattice B == true)
assert(isUpperSemimodular B == true)

///

end;

------------------------------------------
------------------------------------------
-- Extra Code
------------------------------------------
------------------------------------------

restart
needsPackage("Posets", FileName => "./Posets.m2")

