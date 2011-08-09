------------------------------------------
-- Currently caching:
------------------------------------------
-- connectedComponents, coveringRelations, maximalChains, maximalElements, minimalElements, rankFunction,
-- isAtomic, isDistributive, isEulerian, isLowerSemilattice, isLowerSemimodular, isUpperSemilattice, isUpperSemimodular


-- Copyright 2011: David Cook II, Sonja Mapes, Gwyn Whieldon
-- You may redistribute this file under the terms of the GNU General Public
-- License Version 2 as published by the Free Software Foundation.

------------------------------------------
-- Header 
------------------------------------------

if version#"VERSION" <= "1.4" then (
    needsPackage "SimplicialComplexes";
    needsPackage "Graphs";
    )

newPackage select((
    "Posets",
        Version => "1.0.3.1", 
        Date => "09. August 2011",
        Authors => {
            {Name => "David Cook II", Email => "dcook@ms.uky.edu", HomePage => "http://www.ms.uky.edu/~dcook/"},
            {Name => "Sonja Mapes", Email => "smapes@math.duke.edu", HomePage => "http://www.math.duke.edu/~smapes/"},
            {Name => "Gwyn Whieldon", Email => "whieldon@math.cornell.edu", HomePage => "http://www.math.cornell.edu/People/Grads/whieldon.html"}
        },
        Headline => "Package for processing posets and order complexes",
        Configuration => {"DefaultPDFViewer" => "open", "DefaultSuppressLabels" => true},
        DebuggingMode => true,
        if version#"VERSION" > "1.4" then PackageExports => {"SimplicialComplexes", "Graphs"}
        ), x -> x =!= null)

if version#"VERSION" <= "1.4" then (
    needsPackage "SimplicialComplexes";
    needsPackage "Graphs";
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
    -- Derivative combinatorial structures
    "comparabilityGraph",
    "hasseDiagram",
    "incomparabilityGraph",
    "orderComplex",
        "VariableName",
    --
    -- Derivative posets
    "closedInterval",
    "distributiveLattice",
        "OriginalPoset",
  --"dual",
    "filter",
    "flagPoset",
    "naturalLabeling",
    "openInterval",
    "orderIdeal",
    "subposet",
    --
    -- Operations
    "adjoinMax",
    "adjoinMin",
    "augmentPoset",
    "diamondProduct",
    "dropElements",
  --"product",
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
    "monomialPoset",
    "partitionLattice",
        "setPartition",
    "projectivizeArrangement",
    "randomPoset",
        "Bias",
    --
    -- TeX
    "displayPoset",
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
    "coveringRelations",
    "flagChains",
    "isAntichain",
    "linearExtensions",
    "maximalChains",
    --
    -- Enumerative invariants
    "characteristicPolynomial",
    "flagfPolynomial",
    "flaghPolynomial",
    "fPolynomial",
    "hPolynomial",
    "moebiusFunction",
    "rankGeneratingFunction",
    "totalMoebiusFunction",
    "zetaPolynomial",
    --
    -- Properties
  --"height", -- exported by Core
    "isAtomic",
    "isBounded",
    "isConnected",
    "isDistributive",
    "isEulerian",
    "isGraded",
    "isLattice",
    "isLowerSemilattice",
    "isLowerSemimodular",
    "isModular",
    "isRanked",
    "isUpperSemilattice",
    "isUpperSemimodular"
    }

------------------------------------------
-- Non-exported, strongly prevalent functions
------------------------------------------
indexElement := (P,A) -> position(P.GroundSet, i -> i === A);

------------------------------------------
-- Data type & constructor
------------------------------------------
Poset = new Type of HashTable

poset = method()
poset(List, List, Matrix) := Poset => (G, R, M) -> (
    if rank M =!= #G then error "The relations failed anti-symmetry.";
    new Poset from {
        symbol GroundSet => G,
        symbol Relations => R,
        symbol RelationMatrix => M,
        symbol cache => new CacheTable
        })
poset (List, List) := Poset => (G, R) -> poset(G, R, transitiveClosure(G, R))
poset (List, Function) := Poset => (G, cmp) -> (
    try (
        M := matrix for a in G list for b in G list if cmp(a,b) then 1 else 0;
        R := flatten for i to #G-1 list for j to #G-1 list if i != j and M_j_i == 1 then {G_i, G_j} else continue;
    ) else error "The comparison function cmp must (i) take two inputs, (ii) return a Boolean, and (iii) be defined for all pairs of G.";
    poset(G, R, M)
    )
poset List := Poset => R -> poset(unique flatten R, R);
Poset _ ZZ := Thing => (P, i) -> if P.GroundSet#?i then P.GroundSet_i else error "Index out of bounds."

toString Poset := toExternalString Poset := String => P -> "poset(" | toExternalString P.GroundSet | ", " | toExternalString P.Relations | ", " | toString P.RelationMatrix | ")"

-- Returns a matrix M such that M_(i,j) = 1 if G_i <= G_j, and 0 otherwise
transitiveClosure = method()
transitiveClosure (List, List) := Matrix => (G, R) -> (
    idx := hashTable apply(#G, i -> G_i => i);
    R = apply(R, r -> {idx#(first r), idx#(last r)});
    H := floydWarshall digraph hashTable apply(#G, i -> i => set apply(select(R, r -> first r == i), r -> last r));
    matrix apply(#G, i -> apply(#G, j -> if H#(i, j) < 1/0. then 1 else 0))
    )

------------------------------------------
-- Derivative combinatorial structures
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
    idx := hashTable apply(#P.GroundSet, i -> P.GroundSet_i => i);
    cr := apply(coveringRelations P, c -> {idx#(first c), idx#(last c)});
    digraph hashTable apply(#P.GroundSet, i -> i => set apply(select(cr, c -> c_0 == i), c -> c_1))
    )

-- NB: Renames vertices, otherwise it produces the wrong graph in some cases.
incomparabilityGraph = method()
incomparabilityGraph Poset := Graph => P -> (
    E := flatten for i from 0 to #P.GroundSet - 1 list for j from i+1 to #P.GroundSet - 1 list
        if P.RelationMatrix_i_j == 0 and P.RelationMatrix_j_i == 0 then {i, j} else continue;
    fE := unique flatten E;
    graph(E, Singletons => select(#P.GroundSet, i -> not member(i, fE)))
    )

orderComplex = method(Options => { symbol VariableName => getSymbol "v", symbol CoefficientRing => QQ })
orderComplex (Poset) := SimplicialComplex => opts -> (P) -> (
    s := opts.VariableName;
    R := (opts.CoefficientRing)(monoid [s_0..s_(#P.GroundSet - 1)]);
    variableMap := hashTable apply(#P.GroundSet, i -> P.GroundSet#i => R_i);
    simplicialComplex apply(maximalChains P, c -> product apply(c, x -> variableMap#x))
    )

------------------------------------------
-- Derivative posets
------------------------------------------

closedInterval = method()
closedInterval (Poset, Thing, Thing) := Poset => (P, p, q) ->(
    if compare(P, p, q) then subposet(P, select(P.GroundSet, x -> compare(P, p, x) and compare(P, x, q)))
    else if compare(P, q, p) then subposet(P, select(P.GroundSet, x -> compare(P, q, x) and compare(P, x, p)))
    else error "The elements are incomparable."
    )

distributiveLattice = method()
distributiveLattice Poset := Poset => P -> (
    O := unique apply(P.GroundSet, p -> orderIdeal(P, p));
    POI := poset(unique apply(subsets(#O), s -> sort unique flatten O_s), isSubset);
    POI.cache.OriginalPoset = P;
    POI
    )

-- The method dual is given in the Core and has options.
-- As we don't need the options, we discard them.
dual Poset := Poset => {} >> opts -> P -> poset(P.GroundSet, P.Relations/reverse, transpose P.RelationMatrix)

filter = method()
filter (Poset, Thing) := List => (P, a) -> P.GroundSet_(positions(first entries(P.RelationMatrix^{indexElement(P, a)}), i -> i != 0))

flagPoset = method()
flagPoset (Poset, List) := Poset => (P, L)-> (
    if not isRanked P then error "The poset must be ranked.";
    subposet(P, flatten ((rankPoset P)_L))
    )

naturalLabeling = method()
naturalLabeling (Poset, ZZ) := Poset => (P, startIndex) -> (
    F := flatten filtration P;
    renameMap := hashTable for i to #F - 1 list F_i => startIndex + i;
    poset(apply(P.GroundSet, p -> renameMap#p), apply(P.Relations, r -> {renameMap#(first r), renameMap#(last r)}), P.RelationMatrix)            
    )
naturalLabeling Poset := Poset => P -> naturalLabeling(P, 0)

openInterval = method()
openInterval (Poset, Thing, Thing) := Poset => (P, p, q) -> dropElements(closedInterval(P, p, q), {p, q})

orderIdeal = method()
orderIdeal (Poset, Thing) := List => (P, a) -> P.GroundSet_(positions(flatten entries(P.RelationMatrix_{indexElement(P, a)}), i -> i != 0))

subposet = method()
subposet (Poset, List) := Poset => (P, L) -> dropElements(P, toList(set P.GroundSet - set L))

------------------------------------------
-- Operations
------------------------------------------
adjoinMax = method()
adjoinMax (Poset,Thing) := Poset => (P, a) -> 
    poset(P.GroundSet | {a}, 
          P.Relations | apply(P.GroundSet, g-> {g,a}),
          matrix{{P.RelationMatrix, transpose matrix {toList (#P.GroundSet:1)}},{matrix {toList((#P.GroundSet):0)},1}}
          )
adjoinMax Poset := Poset => P -> adjoinMax(P, 1)

adjoinMin = method()
adjoinMin (Poset,Thing) := Poset => (P, a) -> 
    poset({a} | P.GroundSet, 
          apply(P.GroundSet, g -> {a,g}) | P.Relations,
          matrix{{1, matrix{toList (#P.GroundSet:1)}}, {transpose matrix {toList (#P.GroundSet:0)}, P.RelationMatrix}}
          )
adjoinMin Poset := Poset => P -> adjoinMin(P, 0)

augmentPoset = method()
augmentPoset (Poset, Thing, Thing) := Poset => (P, a, b) -> adjoinMin(adjoinMax(P, b), a)
augmentPoset Poset := Poset => P -> adjoinMin adjoinMax P

diamondProduct = method()
diamondProduct (Poset, Poset) := Poset => (P, Q)->(
    if isLattice P and isLattice Q then (
        P':=product(dropElements(P, minimalElements P),dropElements(Q, minimalElements Q));
        poset(prepend({first minimalElements P, first minimalElements Q}, P'.GroundSet), 
              join(apply(minimalElements P', p -> ({first minimalElements P, first minimalElements Q}, p)), P'.Relations))
    ) else error "The posets must be lattices."
    )

dropElements = method()
dropElements (Poset, List) := Poset => (P, L) -> (
    keptIndices := select(toList(0..#P.GroundSet-1), i -> not member(P.GroundSet#i, L));
    newGroundSet := P.GroundSet_keptIndices;
    newRelationMatrix := P.RelationMatrix_keptIndices^keptIndices;
    newRelations := select(allRelations(P, true), r -> not member(first r, L) and not member(last r, L));
    poset(newGroundSet, newRelations, newRelationMatrix)
    )
dropElements (Poset, Thing) := Poset => (P, a) -> dropElements(P, {a})
dropElements (Poset, Function) := Poset => (P, f) -> (
    keptIndices := select(toList(0..#P.GroundSet-1), i-> not f(P.GroundSet#i));
    newGroundSet := apply(keptIndices, i-> P.GroundSet#i);
    newRelationMatrix := P.RelationMatrix_keptIndices^keptIndices;
    newRelations := select(allRelations(P, true), r -> not f(first r) and not f(last r));
    poset(newGroundSet, newRelations, newRelationMatrix)
    )
Poset - Thing := dropElements
Poset - List := dropElements

-- The product method is defined in the Core.
product (Poset, Poset) := Poset => (P, Q) -> 
    poset(flatten for p in P.GroundSet list for q in Q.GroundSet list {p, q},
          join(flatten for c in P.Relations list for q in Q.GroundSet list ({c_0, q}, {c_1, q}),
           flatten for c in Q.Relations list for p in P.GroundSet list ({p, c_0}, {p, c_1})))
Poset * Poset := product

union = method()
union (Poset, Poset) := Poset => (P, Q) -> poset(unique join(P.GroundSet,Q.GroundSet), unique join(P.Relations,Q.Relations))
Poset + Poset := union

------------------------------------------
-- Enumerators
------------------------------------------
booleanLattice = method()
booleanLattice ZZ := Poset => n -> (
    if n < 0 then ( print "Did you mean |n|?"; n = -n; );
    if n == 0 then poset({""}, {}, matrix{{1}}) else (
        Bn1 := booleanLattice(n-1);
        G := apply(Bn1.GroundSet, p -> p | "0") | apply(Bn1.GroundSet, p -> p | "1");
        R := apply(Bn1.Relations, r -> {(first r) | "0", (last r) | "0"}) | 
             apply(Bn1.Relations, r -> {(first r) | "1", (last r) | "1"}) |
             apply(Bn1.GroundSet, p -> {p | "0", p | "1"});
        M := matrix {{Bn1.RelationMatrix, Bn1.RelationMatrix}, {0, Bn1.RelationMatrix}};
        poset(G, R, M)
        )
    )

chain = method()
chain ZZ := Poset => n -> (
    if n == 0 then error "The integer n must be non-zero.";
    if n < 0 then ( print "Did you mean |n|?"; n = -n; );
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
    D := sort (product \ toList@@deepSplice \ toList fold((a,b) -> a ** b, F));
    poset(D, (a,b) -> b % a == 0)
    )

divisorPoset ZZ := Poset => m -> (
    if m == 0 then error "The integer m must be non-zero.";
    if m < 0 then ( print "Did you mean |m|?"; m=-m; );
    if m == 1 then return poset({1}, {}); -- 1 is special
    M := toList \ toList factor m;
    F := apply(M, m -> set apply(last m + 1, i -> (first m)^i));
    -- D is the set of all (positive) divisors of m
    D := sort (product \ toList@@deepSplice \ toList fold((a,b) -> a ** b, F));
    poset(D, (a,b) -> b % a == 0)
    )

divisorPoset (RingElement, RingElement):= Poset =>(m, n) -> (
    if ring m === ring n then (
        if n % m === sub(0, ring m) then (
            P := divisorPoset (n//m);
            poset(apply(P.GroundSet, v -> v * m), apply(P.Relations, r -> (m * first r, m * last r)), P.RelationMatrix)
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
facePoset SimplicialComplex := Poset => D -> (
    testmax := L -> min apply(L, j -> #j) > 1;
    faceset := support \ flatten apply(toList(0..dim D), i -> toList flatten entries faces(i, D));
    chainheads := support \ flatten entries facets D;
    maxchains := apply(chainheads, i-> {i});
    while any(maxchains, testmax) do (
        maxtest := partition(testmax, maxchains);
        holdover := maxtest#false;
        nextstage := flatten apply(maxtest#true, m -> (
            minsize := min apply(m, i -> #i);
            minset := first select(m, i -> #i == minsize);
            coveredfaces := subsets(minset, minsize - 1);
            apply(coveredfaces, c -> append(m, c))
            ));
        maxchains = join(nextstage, holdover);
        );    
    poset(faceset, unique flatten apply(maxchains, i-> apply(subsets(i,2),reverse)))
    )

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

-- Used by lcmLattice for Straegy 1
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

monomialPoset = method()
monomialPoset (MonomialIdeal, ZZ, ZZ) := Poset => (I, minDeg, maxDeg) -> poset(first entries basis(minDeg, maxDeg, quotient I), (m, n) -> n % m == 0)
monomialPoset MonomialIdeal := Poset => I -> poset(first entries basis quotient I, (m, n) -> n % m == 0)

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
        subS := subsets toList(0..i-1);
        M_i = take(subS,{1,#subS-2});
        N_i = unique apply(M_i, r-> sort {r, select(toList(0..i-1), k-> not member(k,r))});
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
    S := coefficientRing R[gens R|{(symbol Z)}];
    newL := apply(L, h->homogenize(sub(h,S),Z));
    G := hyperplaneEquivalence(newL,S);
    rel := hyperplaneInclusions(G,S);
    poset(G,rel)
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

------------------------------------------
-- TeX
------------------------------------------

displayPoset=method(Options => { symbol SuppressLabels => posets'SuppressLabels, symbol PDFViewer => posets'PDFViewer, symbol Jitter => false })
displayPoset(Poset):=opts->(P)->(
    if not instance(opts.PDFViewer, String) then error "The option PDFViewer must be a string.";
    if not instance(opts.SuppressLabels, Boolean) then error "The option SuppressLabels must be a Boolean.";
    if not instance(opts.Jitter, Boolean) then error "The option Jitter must be a Boolean.";
    name := temporaryFileName();
    outputTexPoset(P, concatenate(name, ".tex"), symbol SuppressLabels => opts.SuppressLabels, symbol Jitter => opts.Jitter);
    run concatenate("pdflatex -output-directory /tmp ", name, " 1>/dev/null");
    run concatenate(opts.PDFViewer, " ", name,".pdf &");
    )

outputTexPoset = method(Options => {symbol SuppressLabels => posets'SuppressLabels, symbol Jitter => false});
outputTexPoset(Poset,String) := String => opts -> (P,name)->(
    if not instance(opts.SuppressLabels, Boolean) then error "The option SuppressLabels must be a Boolean.";
    if not instance(opts.Jitter, Boolean) then error "The option Jitter must be a Boolean.";
    fn:=openOut name;
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
    -- hash table of variable labels
    idx:= hashTable apply(#P.GroundSet, i -> P.GroundSet_i => i);
    -- edge list to be read into TikZ
    edgelist:= apply(coveringRelations P, r -> concatenate(toString idx#(first r),"/",toString idx#(last r)));
    -- Find each level of P and set up the positioning of the vertices.
    F := filtration P;
    levelsets := apply(F, v -> #v-1);
    scalew := min{1.5, 15 / (1 + max levelsets)};
    scaleh := min{2 / scalew, 15 / #levelsets};
    halflevelsets := apply(levelsets, lvl -> scalew * lvl / 2);
    spacings := apply(levelsets, lvl -> scalew * toList(0..lvl));
    -- The TeX String
    "\\begin{tikzpicture}[scale=1, vertices/.style={draw, fill=black, circle, inner sep=0pt}]\n" |
    concatenate(
        for i from 0 to #levelsets - 1 list for j from 0 to levelsets_i list
            {"\t\\node [vertices", if opts.SuppressLabels then "]" else (", label=right:{" | tex F_i_j | "}]"),
             " (",toString idx#(F_i_j),") at (-",toString halflevelsets_i,"+",
             toString ((if opts.Jitter then random(scalew*0.2) else 0) + spacings_i_j),",",toString (scaleh*i),"){};\n"}
        ) |
    concatenate("\\foreach \\to/\\from in ", toString edgelist, "\n\\draw [-] (\\to)--(\\from);\n\\end{tikzpicture}\n")
    )

------------------------------------------
-- Vertices & vertex properties
------------------------------------------

atoms = method()
atoms Poset := List => P -> unique apply(select(coveringRelations P, R -> any(minimalElements P, elt -> (elt === R#0))), rels-> rels_1)

compare = method()
compare(Poset, Thing, Thing) := Boolean => (P, a, b) -> (
    aindex := indexElement(P, a);
    bindex := indexElement(P, b);
    P.RelationMatrix_b_a != 0
    )

connectedComponents = method()
connectedComponents Poset := List => P -> (
    if P.cache.?connectedComponents then return P.cache.connectedComponents;
    idx := hashTable apply(#P.GroundSet, i -> P.GroundSet_i => i);
    L := new MutableList from toList(0..#P.GroundSet-1);
    for c in coveringRelations P do (
        i := idx#(c#0); j := idx#(c#1);
        if i < j then (L#j = L#i;) else (L#i = L#j;);
        );
    L = toList L;
    P.cache.connectedComponents = apply(unique L, l -> P.GroundSet_(positions(L, t -> t == l)))
    )

-- Ported from Stembridge's Maple Package
-- F = filtration P; F_0 is the minimal elements of P, F_1 is the minimal elements of P-F_0, &c.
-- Notice that flatten filtration P is a linear extension of P.
filtration = method()
filtration Poset := List => P -> (
    idx := hashTable apply(#P.GroundSet, i-> P.GroundSet_i => i);
    cr := coveringRelations P;
    up := for p in P.GroundSet list apply(select(cr, c -> first c === p), c -> idx#(last c));
    cnt := new MutableList from for p in P.GroundSet list #select(cr, c -> last c === p);
    neu := positions(cnt, c -> c == 0);
    ret := {neu} | while #neu != 0 list neu = for i in flatten up_neu list if cnt#i == 1 then i else ( cnt#i = cnt#i - 1; continue );
    apply(drop(ret, -1), lvl -> P.GroundSet_lvl)
    )

joinExists = method()
joinExists (Poset,Thing,Thing) := Boolean => (P,a,b) -> (
    OIa := filter(P, a);     
    OIb := filter(P, b);
    upperBounds := toList (set(OIa)*set(OIb));
    if upperBounds == {} then false else (
        M := P.RelationMatrix;
        heightUpperBounds := flatten apply(upperBounds, element-> sum entries M_{indexElement(P,element)});
        #(select(heightUpperBounds, i-> i == min heightUpperBounds)) <= 1
        )
    )

joinIrreducibles = method()
joinIrreducibles Poset := List => P -> (
    if not isLattice P then error "The poset is not a lattice.";
    nonComparablePairs := select(subsets(P.GroundSet,2), posspair -> not compare(P, posspair#0,posspair#1) and not compare(P,posspair#1,posspair#0));
    joins := select(unique flatten apply(nonComparablePairs, posspair -> if joinExists(P, posspair#0, posspair#1) then posetMeet(P, posspair#0, posspair#1)), i -> i =!= null); 
    toList (set P.GroundSet - set joins)
    )

maximalElements = method()
maximalElements Poset := List => P -> (
    if P.cache.?maximalElements then return P.cache.maximalElements;
    L := select(#P.GroundSet, i -> all(#P.GroundSet, j -> P.RelationMatrix_(i,j) == 0 or i == j));
    P.cache.maximalElements = P.GroundSet_L
    )

meetExists = method()
meetExists (Poset, Thing, Thing) := Boolean => (P,a,b) -> (
    Fa:= orderIdeal(P, a);
    Fb:= orderIdeal(P, b);
    lowerBounds:= toList (set(Fa)*set(Fb));
    if lowerBounds == {} then false else (
        M := P.RelationMatrix;
        heightLowerBounds := flatten apply(lowerBounds, element-> sum entries M_{indexElement(P,element)});
        #(select(heightLowerBounds, i-> i == max heightLowerBounds)) <= 1
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
    if P.cache.?minimalElements then return P.cache.minimalElements;
    L := select(#P.GroundSet, i -> all(#P.GroundSet, j -> P.RelationMatrix_(j,i) == 0 or i == j));
    P.cache.minimalElements = P.GroundSet_L
    )

posetJoin = method()     
posetJoin (Poset,Thing,Thing) := List => (P,a,b)  -> (
    OIa := filter(P, a);     
    OIb := filter(P, b);
    upperBounds := toList (set(OIa)*set(OIb));
    if upperBounds == {} then error "The elements do not share any upper bounds."
    else (
        M := P.RelationMatrix;
        heightUpperBounds := flatten apply(upperBounds, element-> sum entries M_{indexElement(P,element)});
        if #(select(heightUpperBounds, i-> i == min heightUpperBounds)) > 1 then error "The join does not exist; the least upper bound not unique." 
        else(upperBounds_{position (heightUpperBounds, l -> l == min heightUpperBounds)})
        )
    )

posetMeet = method()
posetMeet (Poset,Thing,Thing) := List => (P,a,b) ->(
    Fa := orderIdeal(P,a);
    Fb := orderIdeal(P,b);
    lowerBounds:= toList (set(Fa)*set(Fb));
    if lowerBounds == {} then error "The elements do not share any lower bounds."
    else (
        M := P.RelationMatrix;
        heightLowerBounds := flatten apply(lowerBounds, element-> sum entries M_{indexElement(P,element)});
        if #(select(heightLowerBounds, i-> i == max heightLowerBounds)) > 1 then error "The meet does not exist; the greatest lower bound not unique." 
        else lowerBounds_{position (heightLowerBounds, l -> l == max heightLowerBounds)}
        )
    )

-- Ported from Stembridge's Maple Package
rankFunction = method()
rankFunction Poset := List => P -> (
    if P.cache.?rankFunction then return P.cache.rankFunction;
    idx := hashTable apply(#P.GroundSet, i-> P.GroundSet_i => i);
    rk := apply(#P.GroundSet, i -> {i, 0});
    for r in apply(coveringRelations P, r -> {idx#(r#0), idx#(r#1)}) do (
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
    if rk === null then error "The poset must be ranked." else apply(max rk + 1, r -> P.GroundSet_(positions(rk, i -> i == r)))
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
antichains Poset := List => P -> (
    v := local v;
    R := (ZZ/2)(monoid [v_1..v_(#P.GroundSet)]);
    S := simplicialComplex monomialIdeal flatten for i from 0 to #P.GroundSet - 1 list for j from i+1 to #P.GroundSet - 1 list 
        if P.RelationMatrix_i_j == 1 or P.RelationMatrix_j_i == 1 then R_i * R_j else continue;
    apply(flatten apply(1 + dim S, d -> flatten entries faces(d, S)), a -> P.GroundSet_(indices a))
    )

coveringRelations = method()
coveringRelations Poset := List => P -> (
    if P.cache.?coveringRelations then return P.cache.coveringRelations;
    gtp := for i to #P.GroundSet - 1 list for j to #P.GroundSet - 1 list if i != j and P.RelationMatrix_j_i != 0 then j else continue;
    P.cache.coveringRelations = flatten for i to #P.GroundSet - 1 list (
        gtgtp := unique flatten gtp_(gtp_i);
        apply(toList(set gtp_i - set gtgtp), j -> {P.GroundSet_i, P.GroundSet_j})
        )
    )

flagChains = method()
flagChains (Poset,List) := List => (P, L) -> (
    if not isRanked P then error "The poset must be ranked.";
    rkP := rankPoset P;
    if #L == 0 then {} else 
    if #L == 1 then apply(rkP_(first L), p -> {p}) else 
    flatten for c in flagChains(P, drop(L, 1)) list for p in rkP_(first L) list if compare(P, p, first c) then prepend(p, c) else continue
    )


isAntichain = method()
isAntichain (Poset, List) := Boolean => (P, L) -> (
    Q := subposet(P, L);
    minimalElements(Q) == maximalElements(Q)
    )

-- Ported from Stembridge's Maple Package
linearExtensions = method()
linearExtensions Poset := List => P -> (
    linExtRec := (G, cr) -> (
        if #cr == 0 then permutations toList G else 
        flatten apply(toList (G - apply(cr, last)), m -> apply(linExtRec(G - {m}, select(cr, c -> first c =!= m)), e -> prepend(m, e)))
        );
    linExtRec(set P.GroundSet, coveringRelations P)
    )

maximalChains = method()
maximalChains Poset := List => P -> (
    if P.cache.?maximalChains then return P.cache.maximalChains;
    nonMaximalChains := apply(minimalElements(P), x -> {x});
    maxChains := {};
    while #nonMaximalChains =!= 0 do (
        nonMaximalChains = flatten apply(nonMaximalChains, c -> (
                nexts := select(coveringRelations P, r -> first r === last c);
                if #nexts == 0 then maxChains = append(maxChains, c);
                apply(nexts, r -> c | {last r})
                )
            )
        );
    P.cache.maximalChains = maxChains
    )

------------------------------------------
-- Enumerative invariants
------------------------------------------

characteristicPolynomial = method(Options => {symbol VariableName => getSymbol "q"})
characteristicPolynomial Poset := RingElement => opts -> P -> (
    if not isGraded P then error "The poset must be graded.";
    rk := rankFunction P;
    mu := totalMoebiusFunction P;
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
    lift(product(gens R, r -> 1 - r)* sub(ff, apply(gens R, r -> r => r/(1 - r))), R)
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

hPolynomial = method(Options => {symbol VariableName => getSymbol "q"})
hPolynomial Poset := RingElement => opts -> P -> (
    fp := fPolynomial(P, opts);
    R := ring fp;
    hp := (1-R_0)^(first degree fp) * sub(fp, R_0 => R_0 / (1 - R_0));
    if denominator hp == -1_R then -numerator hp else numerator hp
    )

moebiusFunction = method()
moebiusFunction Poset := HashTable => P -> ( 
    if #minimalElements P > 1 then error "The poset has more than one minimal element; specify an interval.";
    M := (P.RelationMatrix)^(-1);
    k := position(P.GroundSet,v->v === (minimalElements P)_0);
    hashTable apply(#P.GroundSet,i->{P.GroundSet_i,M_(k,i)})
    )
moebiusFunction (Poset, Thing, Thing) := HashTable => (P, elt1, elt2) -> moebiusFunction closedInterval(P,elt1,elt2)

-- r_i*x^i: r_i is the number of rank i vertices in P
rankGeneratingFunction = method(Options => {symbol VariableName => getSymbol "q"})
rankGeneratingFunction Poset := RingElement => opts -> P -> (
    if not isRanked P then error "The poset must be ranked.";
    R := ZZ(monoid [opts.VariableName]);
    sum(pairs tally rankFunction P, p -> p_1 * (R_0)^(p_0))
    )

totalMoebiusFunction = method()
totalMoebiusFunction Poset := HashTable => P -> (
    idx := hashTable apply(#P.GroundSet, i-> P.GroundSet_i => i);
    mu := new MutableHashTable;
    for p in P.GroundSet do (
        gtp := P.GroundSet_(positions(flatten entries (P.RelationMatrix_(idx#p)), i -> i != 0));
        for q in P.GroundSet do mu#(q, p) = if p === q then 1 else if not member(q, gtp) then 0 else -sum(gtp, z -> if mu#?(q, z) then mu#(q, z) else 0);
        );
    new HashTable from mu
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

-- The method height is given in the Core.
height Poset := ZZ => P -> -1 + max apply (maximalChains P, s-> #s)

isAtomic = method()
isAtomic Poset := Boolean => P -> (
    if P.cache.?isAtomic then return P.cache.isAtomic;
    atm := atoms P;
    P.cache.isAtomic = all(toList(set P.GroundSet - set minimalElements P - set atm), v -> any(atm, a -> compare(P, a, v)))
    )

isBounded = method()
isBounded Poset := Boolean => P -> #minimalElements P == 1 and #maximalElements P == 1

isConnected = method()
isConnected Poset := Boolean => P -> #connectedComponents P == 1

isDistributive = method()
isDistributive Poset := Boolean => P -> (
    if P.cache.?isDistributive then return P.cache.isDistributive;
    if not isLattice P then error "The poset must be a lattice.";
    P.cache.isDistributive = all(subsets(P.GroundSet, 3), G -> posetMeet(P, G_0, first posetJoin(P, G_1, G_2)) == posetJoin(P, first posetMeet(P, G_0, G_1), first posetMeet(P, G_0, G_2)))
    )

isEulerian = method()
isEulerian Poset := Boolean => P -> (
    if P.cache.?isEulerian then return P.cache.isEulerian;
    rk := rankFunction P;
    if rk === null then error "The poset must be ranked.";
    idx := hashTable apply(#P.GroundSet, i-> P.GroundSet_i => i);
    mu := totalMoebiusFunction P;
    P.cache.isEulerian = all(P.GroundSet, 
        p -> (
            gtp := P.GroundSet_(positions(flatten entries (P.RelationMatrix_(idx#p)), i -> i != 0));
            all(gtp, q -> mu#(q, p) == (-1)^(rk#(idx#q) - rk#(idx#p)))
            )
        )
    )

isGraded = method()
isGraded Poset := Boolean => P -> #unique apply(maximalChains P, c -> #c) == 1

isLattice = method()
isLattice Poset := Boolean => P -> isLowerSemilattice P and isUpperSemilattice P 

isLowerSemilattice = method()
isLowerSemilattice Poset := Boolean => P -> if P.cache.?isLowerSemilattice then P.cache.isLowerSemilattice else
    P.cache.isLowerSemilattice = all(0..#P.GroundSet-1, i -> all(i+1..#P.GroundSet-1, j -> joinExists(P, P.GroundSet#i, P.GroundSet#j)))

-- Ported from Stembridge's Maple Package
isLowerSemimodular = method()
isLowerSemimodular Poset := Boolean => P -> (
    if P.cache.?isLowerSemimodular then return P.cache.isLowerSemimodular;
    if not isLattice P then error "The poset must be a lattice.";
    idx := hashTable apply(#P.GroundSet, i -> P.GroundSet_i => i);
    cr := coveringRelations P;
    cvrs := for a in P.GroundSet list for c in cr list if c_1 === a then idx#(c_0) else continue;
    P.cache.isLowerSemimodular = all(#P.GroundSet, i -> all(#cvrs#i, j -> all(j, k -> #(set cvrs#(cvrs#i#j) * set cvrs#(cvrs#i#k)) === 1)))
    )

isModular = method()
isModular Poset := Boolean => P -> (
    if not isLattice P then error "The poset must be a lattice.";
    isLowerSemimodular P and isUpperSemimodular P
    )

isRanked = method()
isRanked Poset := Boolean => P -> rankFunction P =!= null

isUpperSemilattice = method()
isUpperSemilattice Poset := Boolean => P -> if P.cache.?isUpperSemilattice then P.cache.isLowerSemilattice else
    P.cache.isUpperSemilattice = all(0..#P.GroundSet-1, i -> all(i+1..#P.GroundSet-1, j -> meetExists(P, P.GroundSet#i, P.GroundSet#j)))

-- Ported from Stembridge's Maple Package
isUpperSemimodular = method()
isUpperSemimodular Poset := Boolean => P -> (
    if P.cache.?isUpperSemimodular then return P.cache.isUpperSemimodular;
    if not isLattice P then error "The poset must be a lattice.";
    idx := hashTable apply(#P.GroundSet, i -> P.GroundSet_i => i);
    cr := coveringRelations P;
    cvrby := for a in P.GroundSet list for c in cr list if c_0 === a then idx#(c_1) else continue;
    P.cache.isUpperSemimodular = all(#P.GroundSet, i -> all(#cvrby#i, j -> all(j, k -> #(set cvrby#(cvrby#i#j) * set cvrby#(cvrby#i#k)) === 1)))
    )

------------------------------------------
-- Documentation
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
///

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
            P = poset(G, R)                 -- the poset with matrix computed
    SeeAlso
        poset
///

-----------
-- METHODS
-----------

-- _
doc ///
    Key
        (symbol _,Poset,ZZ)
    Headline
        gets an element of the ground set
    Usage
        P_i
    Inputs
        P:Poset
        i:ZZ
    Outputs
        a:Thing
    Description
        Text
            TODO
    SeeAlso
        Posets
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
        TODO
    Inputs
        G:List
        R:List
        M:Matrix
        cmp:Function
    Outputs
        P:Poset
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- transitiveClosure
doc ///
    Key
        transitiveClosure
        (transitiveClosure,List,List)
    Headline
        computes the transitive closure of a set of relations
    Usage
        TODO
    Inputs
        G:List
        R:List
    Outputs
        M:Matrix
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- comparabilityGraph
doc ///
    Key
        comparabilityGraph
        (comparabilityGraph,Poset)
    Headline
        produces the comparability graph of a poset
    Usage
        TODO
    Inputs
        P:Poset
    Outputs
        G:Graph
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- hasseDiagram
doc ///
    Key
        hasseDiagram
        (hasseDiagram,Poset)
    Headline
        produces the Hasse diagram of a poset
    Usage
        TODO
    Inputs
        P:Poset
    Outputs
        D:Digraph
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- incomparabilityGraph
doc ///
    Key
        incomparabilityGraph
        (incomparabilityGraph,Poset)
    Headline
        produces the incomparability graph of a poset
    Usage
        TODO
    Inputs
        P:Poset
    Outputs
        G:Graph
    Description
        Text
            TODO
    SeeAlso
        Posets
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
        TODO
    Inputs
        P:Poset
        VariableName=>Symbol
        CoefficientRing=>Ring
    Outputs
        O:SimplicialComplex
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- closedInterval
doc ///
    Key
        closedInterval
        (closedInterval,Poset,Thing,Thing)
    Headline
        computes the subposet contained between two points
    Usage
        TODO
    Inputs
        P:Poset
        p:Thing
        q:Thing
    Outputs
        I:Poset
    Description
        Text
            TODO
    SeeAlso
        Posets
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
        TODO
    Inputs
        P:Poset
    Outputs
        L:Poset
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- dual
doc ///
    Key
        (dual,Poset)
    Headline
        produces the derived poset with relations reversed
    Usage
        TODO
    Inputs
        P:Poset
    Outputs
        P':Poset
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- filter
doc ///
    Key
        filter
        (filter,Poset,Thing)
    Headline
        computes the elements above a given element in a poset
    Usage
        TODO
    Inputs
        P:Poset
        a:Thing
    Outputs
        L:List
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- flagPoset
doc ///
    Key
        flagPoset
        (flagPoset,Poset,List)
    Headline
        computes the subposet of specified ranks of a ranked poset
    Usage
        TODO
    Inputs
        P:Poset
        L:List
    Outputs
        F:Poset
    Description
        Text
            TODO
    SeeAlso
        Posets
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
        TODO
    Inputs
        P:Poset
    Outputs
        Q:Poset
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- openInterval
doc ///
    Key
        openInterval
        (openInterval,Poset,Thing,Thing)
    Headline
        computes the subposet contained strictly between two points
    Usage
        TODO
    Inputs
        P:Poset
        a:Thing
        b:Thing
    Outputs
        I:Poset
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- orderIdeal
doc ///
    Key
        orderIdeal
        (orderIdeal,Poset,Thing)
    Headline
        computes the elements below a given element in a poset
    Usage
        TODO
    Inputs
        P:Poset
        a:Thing
    Outputs
        L:List
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- subposet
doc ///
    Key
        subposet
        (subposet,Poset,List)
    Headline
        computes the induced subposet of a poset given a list of elements
    Usage
        TODO
    Inputs
        P:Poset
        L:List
    Outputs
        Q:Poset
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- adjoinMax
doc ///
    Key
        adjoinMax
        (adjoinMax,Poset)
        (adjoinMax,Poset,Thing)
    Headline
        computes the poset with a new maximum element
    Usage
        TODO
    Inputs
        P:Poset
        a:Thing
    Outputs
        Q:Poset
    Description
        Text
            TODO
    SeeAlso
        Posets
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
        TODO
    Inputs
        P:Poset
        a:Thing
    Outputs
        Q:Poset
    Description
        Text
            TODO
    SeeAlso
        Posets
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
        TODO
    Inputs
        P:Poset
        a:Thing
        b:Thing
    Outputs
        Q:Poset
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- diamondProduct
doc ///
    Key
        diamondProduct
        (diamondProduct,Poset,Poset)
    Headline
        computes the diamond product of two lattices
    Usage
        TODO
    Inputs
        P:Poset
        Q:Poset
    Outputs
        D:Poset
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- dropElements
doc ///
    Key
        dropElements
        (dropElements,Poset,Thing)
        (dropElements,Poset,Function)
        (dropElements,Poset,List)
        (symbol -,Poset,Thing)
        (symbol -,Poset,List)
    Headline
        computes the induced subposet of a poset given a list of elements to remove
    Usage
        TODO
    Inputs
        P:Poset
        a:Thing
        L:List
        f:Function
    Outputs
        Q:Poset
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- product
doc ///
    Key
        (product,Poset,Poset)
        (symbol *,Poset,Poset)
    Headline
        computes the product of two posets
    Usage
        TODO
    Inputs
        P:Poset
        Q:Poset
    Outputs
        R:Poset
    Description
        Text
            TODO
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
        TODO
    Inputs
        P:Poset
        Q:Poset
    Outputs
        R:Poset
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- booleanLattice
doc ///
    Key
        booleanLattice
        (booleanLattice,ZZ)
    Headline
        generates the $n$-boolean lattice
    Usage
        TODO
    Inputs
        n:ZZ
    Outputs
        B:Poset
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- chain
doc ///
    Key
        chain
        (chain,ZZ)
    Headline
        generates the $n$-chain poset
    Usage
        TODO
    Inputs
        n:ZZ
    Outputs
        C:Poset
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- divisorPoset
doc ///
    Key
        divisorPoset
        (divisorPoset,ZZ)
    Headline
        generates the poset of divisors
    Usage
        TODO
    Inputs
        n:ZZ
    Outputs
        P:Poset
    Description
        Text
            TODO
    SeeAlso
        Posets
///

doc ///
    Key
        (divisorPoset,RingElement)
    Headline
        generates the poset of divisors
    Usage
        TODO
    Inputs
        m:RingElement
    Outputs
        P:Poset
    Description
        Text
            TODO
    SeeAlso
        Posets
///

doc ///
    Key
        (divisorPoset,RingElement,RingElement)
    Headline
        generates the poset of divisors
    Usage
        TODO
    Inputs
        m:RingElement
        n:RingElement
    Outputs
        P:Poset
    Description
        Text
            TODO
    SeeAlso
        Posets
///

doc ///
    Key
        (divisorPoset,List,List,PolynomialRing)
    Headline
        generates the poset of divisors
    Usage
        TODO
    Inputs
        m:List
        n:List
        R:PolynomialRing
    Outputs
        P:Poset
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- dominanceLattice
doc ///
    Key
        dominanceLattice
        (dominanceLattice,ZZ)
    Headline
        generates the dominance lattice of partitions of $n$
    Usage
        TODO
    Inputs
        n:ZZ
    Outputs
        P:Poset
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- facePoset
doc ///
    Key
        facePoset
        (facePoset,SimplicialComplex)
    Headline
        generates the face poset of a simplicial complex
    Usage
        TODO
    Inputs
        D:SimplicialComplex
    Outputs
        F:Poset
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- intersectionLattice
doc ///
    Key
        intersectionLattice
        (intersectionLattice,List,Ring)
    Headline
        generates the intersection lattice of a hyperplane arrangement
    Usage
        TODO
    Inputs
        L:List
        R:Ring
    Outputs
        P:Poset
    Description
        Text
            TODO
    SeeAlso
        Posets
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
        TODO
    Inputs
        M:MonomialIdeal
        I:Ideal
        Strategy=>ZZ
    Outputs
        P:Poset
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- monomialPoset
doc ///
    Key
        monomialPoset
        (monomialPoset,MonomialIdeal)
        (monomialPoset,MonomialIdeal,ZZ,ZZ)
    Headline
        generates the poset of divisibility in the monomial basis of an ideal
    Usage
        TODO
    Inputs
        I:MonomialIdeal
        minDeg:ZZ
        maxDeg:ZZ
    Outputs
        P:Poset
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- partitionLattice
doc ///
    Key
        partitionLattice
        (partitionLattice,ZZ)
    Headline
        computes the lattice of set-partitions of size $n$
    Usage
        TODO
    Inputs
        n:ZZ
    Outputs
        P:Poset
    Description
        Text
            TODO
    SeeAlso
        Posets
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
        TODO
    Inputs
        n:ZZ
    Outputs
        L:List
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- projectivizeArrangement
doc ///
    Key
        projectivizeArrangement
        (projectivizeArrangement,List,Ring)
    Headline
        computes the intersection poset of a projectivized hyperplane arrangement
    Usage
        TODO
    Inputs
        L:List
        R:Ring
    Outputs
        P:Poset
    Description
        Text
            TODO
    SeeAlso
        Posets
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
        generates a random poset with a given edge probability
    Usage
        TODO
    Inputs
        n:ZZ
        G:List
        Bias=>RR
    Outputs
        P:Poset
    Description
        Text
            TODO
    SeeAlso
        Posets
///

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
        TODO
    Inputs
        P:Poset
        SuppressLabels=>Boolean
        PDFViewer=>String
        Jitter=>Boolean
    Outputs
        n:Nothing
    Description
        Text
            TODO
    SeeAlso
        Posets
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
        TODO
    Inputs
        P:Poset
        SuppressLabels=>Boolean
        Jitter=>Boolean
    Outputs
        n:Nothing
    Description
        Text
            TODO
    SeeAlso
        Posets
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
    Headline
        generates a string containg a TikZ-figure of a poset
    Usage
        TODO
    Inputs
        P:Poset
        SuppressLabels=>Boolean
        Jitter=>Boolean
    Outputs
        S:String
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- atoms
doc ///
    Key
        atoms
        (atoms,Poset)
    Headline
        computes the list of elements covering the minimal elements of a poset
    Usage
        TODO
    Inputs
        P:Poset
    Outputs
        A:List
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- compare
doc ///
    Key
        compare
        (compare,Poset,Thing,Thing)
    Headline
        compares two elements in a poset
    Usage
        TODO
    Inputs
        P:Poset
        a:Thing
        b:Thing
    Outputs
        r:Boolean
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- connectedComponents
doc ///
    Key
        connectedComponents
        (connectedComponents,Poset)
    Headline
        generates a list of connected components of a poset
    Usage
        TODO
    Inputs
        P:Poset
    Outputs
        C:List
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- filtration
doc ///
    Key
        filtration
        (filtration,Poset)
    Headline
        generates the filtration of a posett
    Usage
        TODO
    Inputs
        P:Poset
    Outputs
        F:List
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- joinExists
doc ///
    Key
        joinExists
        (joinExists,Poset,Thing,Thing)
    Headline
        determines if the join exists for two elements of a poset
    Usage
        TODO
    Inputs
        P:Poset
        a:Thing
        b:Thing
    Outputs
        j:Boolean
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- joinIrreducibles
doc ///
    Key
        joinIrreducibles
        (joinIrreducibles,Poset)
    Headline
        determines the join irreducible elements of a poset
    Usage
        TODO
    Inputs
        P:Poset
    Outputs
        J:List
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- maximalElements
doc ///
    Key
        maximalElements
        (maximalElements,Poset)
    Headline
        determines the maximal elements of a poset
    Usage
        TODO
    Inputs
        P:Poset
    Outputs
        M:List
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- meetExists
doc ///
    Key
        meetExists
        (meetExists,Poset,Thing,Thing)
    Headline
        determines if the meet exists for two elements of a poset
    Usage
        TODO
    Inputs
        P:Poset
        a:Thing
        b:Thing
    Outputs
        m:Boolean
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- meetIrreducibles
doc ///
    Key
        meetIrreducibles
        (meetIrreducibles,Poset)
    Headline
        determines the meet irreducible elements of a poset
    Usage
        TODO
    Inputs
        P:Poset
    Outputs
        M:List
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- minimalElements
doc ///
    Key
        minimalElements
        (minimalElements,Poset)
    Headline
        determines the minimal elements of a poset
    Usage
        TODO
    Inputs
        P:Poset
    Outputs
        M:List
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- posetJoin
doc ///
    Key
        posetJoin
        (posetJoin,Poset,Thing,Thing)
    Headline
        determines the join for two elements of a poset
    Usage
        TODO
    Inputs
        P:Poset
        a:Thing
        b:Thing
    Outputs
        j:Thing
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- posetMeet
doc ///
    Key
        posetMeet
        (posetMeet,Poset,Thing,Thing)
    Headline
        determines the meet for two elements of a poset
    Usage
        TODO
    Inputs
        P:Poset
        a:Thing
        b:Thing
    Outputs
        m:Thing
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- rankFunction
doc ///
    Key
        rankFunction
        (rankFunction,Poset)
    Headline
        computes the rank function of a ranked poset
    Usage
        TODO
    Inputs
        P:Poset
    Outputs
        rk:List
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- rankPoset
doc ///
    Key
        rankPoset
        (rankPoset,Poset)
    Headline
        generates a list of lists representing the ranks of a ranked poset
    Usage
        TODO
    Inputs
        P:Poset
    Outputs
        L:List
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- allRelations
doc ///
    Key
        allRelations
        (allRelations,Poset)
        (allRelations,Poset,Boolean)
    Headline
        computes all relations of a poset
    Usage
        TODO
    Inputs
        P:Poset
        NoLoops:Boolean
    Outputs
        R:List
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- antichains
doc ///
    Key
        antichains
        (antichains,Poset)
    Headline
        computes all antichains of a poset
    Usage
        TODO
    Inputs
        P:Poset
    Outputs
        L:List
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- coveringRelations
doc ///
    Key
        coveringRelations
        (coveringRelations,Poset)
    Headline
        computes the minimal list of generating relations of a poset
    Usage
        TODO
    Inputs
        P:Poset
    Outputs
        R:List
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- flagChains
doc ///
    Key
        flagChains
        (flagChains,Poset,List)
    Headline
        computes the maximal chains in a list of flags of a ranked poset
    Usage
        TODO
    Inputs
        P:Poset
        L:List
    Outputs
        C:List
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- isAntichain
doc ///
    Key
        isAntichain
        (isAntichain,Poset,List)
    Headline
        determines if a given list of vertices is an antichain of a poset
    Usage
        TODO
    Inputs
        P:Poset
        L:List
    Outputs
        i:Boolean
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- linearExtensions
doc ///
    Key
        linearExtensions
        (linearExtensions,Poset)
    Headline
        computes all linear extensions of a poset
    Usage
        TODO
    Inputs
        P:Poset
    Outputs
        L:List
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- maximalChains
doc ///
    Key
        maximalChains
        (maximalChains,Poset)
    Headline
        computes all maximal chains of a poset
    Usage
        TODO
    Inputs
        P:Poset
    Outputs
        M:List
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- characteristicPolynomial
doc ///
    Key
        characteristicPolynomial
        (characteristicPolynomial,Poset)
        [characteristicPolynomial,VariableName]
    Headline
        computes the characteristic polynomial of a graded poset
    Usage
        TODO
    Inputs
        P:Poset
        VariableName=>Symbol
    Outputs
        p:RingElement
    Description
        Text
            TODO
    SeeAlso
        Posets
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
        TODO
    Inputs
        P:Poset
        VariableName=>Symbol
    Outputs
        ff:RingElement
    Description
        Text
            TODO
    SeeAlso
        Posets
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
        TODO
    Inputs
        P:Poset
        VariableName=>Symbol
    Outputs
        fh:RingElement
    Description
        Text
            TODO
    SeeAlso
        Posets
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
        TODO
    Inputs
        P:Poset
        VariableName=>Symbol
    Outputs
        f:RingElement
    Description
        Text
            TODO
    SeeAlso
        Posets
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
        TODO
    Inputs
        P:Poset
        VariableName=>Symbol
    Outputs
        h:RingElement
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- moebiusFunction
doc ///
    Key
        moebiusFunction
        (moebiusFunction,Poset)
        (moebiusFunction,Poset,Thing,Thing)
    Headline
        computes the Moebius function of a poset with a unique minimal element
    Usage
        TODO
    Inputs
        P:Poset
        a:Thing
        b:Thing
    Outputs
        mu:HashTable
    Description
        Text
            TODO
    SeeAlso
        Posets
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
        TODO
    Inputs
        P:Poset
        VariableName=>Symbol
    Outputs
        r:RingElement
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- totalMoebiusFunction
doc ///
    Key
        totalMoebiusFunction
        (totalMoebiusFunction,Poset)
    Headline
        computes the Moebius function at every pair of elements of a poset
    Usage
        TODO
    Inputs
        P:Poset
    Outputs
        mu:HashTable
    Description
        Text
            TODO
    SeeAlso
        Posets
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
        TODO
    Inputs
        P:Poset
        VariableName=>Symbol
    Outputs
        z:RingElement
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- height
doc ///
    Key
        (height,Poset)
    Headline
        computes the height of a poset
    Usage
        TODO
    Inputs
        P:Poset
    Outputs
        h:ZZ
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- isAtomic
doc ///
    Key
        isAtomic
        (isAtomic,Poset)
    Headline
        determines if a poset is atomic
    Usage
        TODO
    Inputs
        P:Poset
    Outputs
        i:Boolean
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- isBounded
doc ///
    Key
        isBounded
        (isBounded,Poset)
    Headline
        determines if a poset is bounded
    Usage
        TODO
    Inputs
        P:Poset
    Outputs
        i:Boolean
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- isConnected
doc ///
    Key
        isConnected
        (isConnected,Poset)
    Headline
        determines if a poset is connected
    Usage
        TODO
    Inputs
        P:Poset
    Outputs
        i:Boolean
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- isDistributive
doc ///
    Key
        isDistributive
        (isDistributive,Poset)
    Headline
        determines if a lattice is distributive
    Usage
        TODO
    Inputs
        P:Poset
    Outputs
        i:Boolean
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- isEulerian
doc ///
    Key
        isEulerian
        (isEulerian,Poset)
    Headline
        determines if a ranked poset is Eulerian
    Usage
        TODO
    Inputs
        P:Poset
    Outputs
        i:Boolean
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- isGraded
doc ///
    Key
        isGraded
        (isGraded,Poset)
    Headline
        determines if a poset is graded
    Usage
        TODO
    Inputs
        P:Poset
    Outputs
        i:Boolean
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- isLattice
doc ///
    Key
        isLattice
        (isLattice,Poset)
    Headline
        determines if a poset is a lattice
    Usage
        TODO
    Inputs
        P:Poset
    Outputs
        i:Boolean
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- isLowerSemilattice
doc ///
    Key
        isLowerSemilattice
        (isLowerSemilattice,Poset)
    Headline
        determines if a poset is a lower (or meet) semilattice
    Usage
        TODO
    Inputs
        P:Poset
    Outputs
        i:Boolean
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- isLowerSemimodular
doc ///
    Key
        isLowerSemimodular
        (isLowerSemimodular,Poset)
    Headline
        determines if a lattice is lower (or meet) semimodular
    Usage
        TODO
    Inputs
        P:Poset
    Outputs
        i:Boolean
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- isModular
doc ///
    Key
        isModular
        (isModular,Poset)
    Headline
        determines if a lattice is modular
    Usage
        TODO
    Inputs
        P:Poset
    Outputs
        i:Boolean
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- isRanked
doc ///
    Key
        isRanked
        (isRanked,Poset)
    Headline
        determines if a poste is ranked
    Usage
        TODO
    Inputs
        P:Poset
    Outputs
        i:Boolean
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- isUpperSemilattice
doc ///
    Key
        isUpperSemilattice
        (isUpperSemilattice,Poset)
    Headline
        determines if a poset is a upper (or join) semilattice
    Usage
        TODO
    Inputs
        P:Poset
    Outputs
        i:Boolean
    Description
        Text
            TODO
    SeeAlso
        Posets
///

-- isUpperSemimodular
doc ///
    Key
        isUpperSemimodular
        (isUpperSemimodular,Poset)
    Headline
        determines if a lattice is upper (or join) semimoudlar
    Usage
        TODO
    Inputs
        P:Poset
    Outputs
        i:Boolean
    Description
        Text
            TODO
    SeeAlso
        Posets
///

undocumented { "VariableName", (toExternalString,Poset), (toString,Poset) };

------------------------------------------
-- Tests
------------------------------------------

end;

------------------------------------------
-- Extra Code
------------------------------------------
restart
needsPackage("Posets", FileName => "./Posets.m2")

