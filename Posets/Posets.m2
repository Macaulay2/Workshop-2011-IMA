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
        Version => "1.0.2", 
        Date => "02. August 2011",
        Authors => {
            {Name => "Sonja Mapes", Email => "smapes@math.duke.edu", HomePage => "http://www.math.duke.edu/~smapes/"},
            {Name => "Gwyn Whieldon", Email => "whieldon@math.cornell.edu", HomePage => "http://www.math.cornell.edu/People/Grads/whieldon.html"},
            {Name => "David Cook II", Email => "dcook@ms.uky.edu", HomePage => "http://www.ms.uky.edu/~dcook/"}
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
    "dualPoset",
    "filter",
    "flagPoset",
    "openInterval",
    "orderIdeal",
    "subPoset",
    --
    -- Operations
    "adjoinMax",
    "adjoinMin",
    "augmentPoset",
    "dropElements",
    "mergePoset",
    "posetDiamondProduct",
    "posetProduct",
    --
    -- Enumerators
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
poset(List, List, Matrix) := Poset => (I,C,M) -> (
    if rank M =!= #I then error "The relations failed anti-symmetry.";
    new Poset from {
        symbol GroundSet => I,
        symbol Relations => C,
        symbol RelationMatrix => M,
        symbol cache => new CacheTable
        })
poset (List, List) := Poset => (I, C) -> poset(I, C, transitiveClosure(I, C))
poset (List, Function) := Poset => (I, cmp) -> (
    try (
        rel := flatten for a in I list for b in I list if cmp(a,b) then {a,b} else continue;
    ) else error "The comparison function cmp must (i) take two inputs, (ii) return a Boolean, and (iii) be defined for all pairs of I.";
    poset(I, rel)
    )
poset List := Poset => C -> poset(unique flatten C, C);

--input: (I,C).  I=List of vertices.  C=List of pairs (edges)
--output: matrix where 1 in (i,j) position where i <= j, 0 otherwise
transitiveClosure = method()
transitiveClosure (List,List) := Matrix => (I, C) -> (
     idx := hashTable apply(#I, i-> I_i => i);
     G := floydWarshall digraph hashTable apply(I, v -> idx#v => set apply(select(C, e -> e_0 === v),e -> idx#(e_1)));
     matrix apply(I, u -> apply(I, v -> if G#(idx#u, idx#v) < 1/0. then 1 else 0))
     )

------------------------------------------
-- Derivative combinatorial structures
------------------------------------------

comparabilityGraph = method()
comparabilityGraph Poset := Graph => P -> (
    E := flatten for i from 0 to #P.GroundSet - 1 list for j from i+1 to #P.GroundSet - 1 list
        if P.RelationMatrix_i_j == 1 or P.RelationMatrix_j_i == 1 then {P.GroundSet_i, P.GroundSet_j} else continue;
    fE := unique flatten E;
    graph(E, Singletons => select(P.GroundSet, p -> not member(p, fE)))
    )

hasseDiagram = method()
hasseDiagram Poset := Digraph => P -> (
    cr := coveringRelations P;
    digraph hashTable apply(P.GroundSet, v -> v => set apply(select(cr, e -> e_0 === v), e -> e_1))
    )

incomparabilityGraph = method()
incomparabilityGraph Poset := Graph => P -> (
    E := flatten for i from 0 to #P.GroundSet - 1 list for j from i+1 to #P.GroundSet - 1 list
        if P.RelationMatrix_i_j == 0 and P.RelationMatrix_j_i == 0 then {P.GroundSet_i, P.GroundSet_j} else continue;
    fE := unique flatten E;
    graph(E, Singletons => select(P.GroundSet, p -> not member(p, fE)))
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

-- input:  poset, and two elements
-- output:  the induced poset with minimal element and maximal element corresponding to the 2 given elements
closedInterval = method()
closedInterval (Poset, Thing, Thing) := Poset => (P, elt1, elt2) ->(
    if compare(P, elt1, elt2) then subPoset(P, select(P.GroundSet, elt -> compare(P, elt1, elt) and compare(P, elt, elt2)))
    else if compare(P, elt2, elt1) then subPoset(P, select(P.GroundSet, elt -> compare(P, elt2, elt) and compare(P, elt, elt1)))
    else error "The elements are incomparable."
    )

distributiveLattice = method()
distributiveLattice Poset := Poset => P -> (
    O := unique apply(P.GroundSet, p -> orderIdeal(P, p));
    POI := poset(unique apply(subsets(#O), s -> sort unique flatten O_s), isSubset);
    POI.cache.OriginalPoset = P;
    POI
    )

dualPoset = method()
dualPoset Poset := Poset => P -> poset(P.GroundSet, P.Relations/reverse)

-- input: a poset, and an element from I
-- output:  the filter of a, i.e. all elements in the poset that are >= a
filter = method()
filter (Poset, Thing) := List => (P, a) -> P.GroundSet_(positions(first entries(P.RelationMatrix^{indexElement(P, a)}), i -> i != 0))

flagPoset = method()
flagPoset (Poset, List) := Poset => (P, L)-> subPoset(P, flatten ((rankPoset P)_L))

-- input: poset and two elements
-- output: the induced poset coming from the poset with minimal element and maximal element corresponding to the 2 given elements with these 2 elements removed 
openInterval = method()
openInterval (Poset, Thing, Thing) := Poset => (P, elt1, elt2) -> dropElements(closedInterval(P, elt1, elt2), {elt1, elt2})

-- input: a poset, and an element from I
-- output: the order ideal of a, i.e. all elements in the poset that are <= a
orderIdeal = method()
orderIdeal (Poset, Thing) := List => (P, a) -> P.GroundSet_(positions(flatten entries(P.RelationMatrix_{indexElement(P, a)}), i -> i != 0))

-- inputs:  a poset P and a list L of elements from P to "keep"
-- outputs:  induced poset the list L
subPoset = method()
subPoset (Poset, List) := Poset => (P, L) -> dropElements(P, toList(set P.GroundSet - set L))

------------------------------------------
-- Operations
------------------------------------------
--inputs:  Poset P, Thing a
--outputs:  new Poset P' with a as label for max or min
adjoinMax = method()
adjoinMax (Poset,Thing) := Poset =>(P,a)-> poset(P.GroundSet | {a}, P.Relations | apply(P.GroundSet, g-> {g,a}))
adjoinMax Poset := Poset => P -> adjoinMax(P, {1})

adjoinMin = method()
adjoinMin (Poset,Thing) :=  Poset => (P,a)-> poset(P.GroundSet | {a}, P.Relations | apply(P.GroundSet, g-> {a,g}))
adjoinMin Poset := Poset => P -> adjoinMin(P, {0})

augmentPoset = method()
augmentPoset (Poset, Thing, Thing) := Poset => (P, a, b) -> adjoinMin(adjoinMax(P, b), a)
augmentPoset Poset := Poset => P -> adjoinMin adjoinMax P

-- inputs:  poset P and a list L of elements to drop
-- outputs: P without L
dropElements = method()
dropElements (Poset, List) := Poset => (P, L) -> (
    keptIndices := select(toList(0..#P.GroundSet-1), i -> not member(P.GroundSet#i, L));
    newGroundSet := P.GroundSet_keptIndices;
    newRelationMatrix := P.RelationMatrix_keptIndices^keptIndices;
    newRelations := select(allRelations(P, true), r -> not member(first r, L) and not member(last r, L));
    poset(newGroundSet, newRelations, newRelationMatrix)
    )
dropElements (Poset, Function) := Poset => (P, f) -> (
    keptIndices := select(toList(0..#P.GroundSet-1), i-> not f(P.GroundSet#i));
    newGroundSet := apply(keptIndices, i-> P.GroundSet#i);
    newRelationMatrix := P.RelationMatrix_keptIndices^keptIndices;
    newRelations := select(allRelations(P, true), r -> not f(first r) and not f(last r));
    poset(newGroundSet, newRelations, newRelationMatrix)
    )

mergePoset = method()
mergePoset (Poset, Poset) := Poset => (P, Q) -> poset(unique join(P.GroundSet,Q.GroundSet), unique join(P.Relations,Q.Relations))

posetDiamondProduct = method()
posetDiamondProduct (Poset, Poset) := Poset => (P, Q)->(
    if isLattice P and isLattice Q then (
        P':=posetProduct(dropElements(P, minimalElements P),dropElements(Q, minimalElements Q));
        poset(prepend({first minimalElements P, first minimalElements Q}, P'.GroundSet), 
              join(apply(minimalElements P', p -> ({first minimalElements P, first minimalElements Q}, p)), P'.Relations))
    ) else error "The posets must be lattices."
    )

posetProduct = method()
posetProduct (Poset, Poset) := Poset => (P, Q) -> 
    poset(flatten for p in P.GroundSet list for q in Q.GroundSet list {p, q},
          join(flatten for c in P.Relations list for q in Q.GroundSet list ({c_0, q}, {c_1, q}),
           flatten for c in Q.Relations list for p in P.GroundSet list ({p, c_0}, {p, c_1})))

------------------------------------------
-- Enumerators
------------------------------------------
chain = method()
chain ZZ := Poset => n -> (
    if n == 0 then error "The integer n must be non-zero.";
    if n < 0 then ( print "Did you mean |n|?"; n = -n; );
    -- The matrix is known, so give it.
    poset(toList(1..n), apply(n-1, i -> {i+1, i+2}), matrix toList apply(1..n, i -> toList join((i-1):0, (n-i+1):1)))
    )

-- input:  a monomial m (and an ideal I)
-- output: lattice of all monomials dividing m (and contained in I)
divisorPoset = method()
divisorPoset RingElement := Poset => m -> (
    allMultiDegreesLessThan := d -> (
        L := {{}};
        for i from 0 to #d - 1 do L = flatten apply(L, H -> apply(d#i + 1, i -> H | {i}));
        L
        );
    makeMonomialFromDegree := (R, d) -> product apply(numgens R, i-> R_i^(d#i));
    d := flatten exponents m;
    Ground := apply(allMultiDegreesLessThan d, e -> makeMonomialFromDegree(ring m, e));
    Rels :=  unique flatten apply (Ground, r-> apply(Ground, s-> if s % r == 0 then (r,s)));
    Rels = select(Rels, r -> r =!= null);
    RelsMatrix :=  matrix apply (Ground, r-> apply(Ground, s-> if s%r == 0 then 1 else 0));
    poset (Ground, Rels, RelsMatrix)
    )

divisorPoset ZZ := Poset => m -> (
    if m == 0 then error "The integer m must be non-zero.";
    if m < 0 then ( print "Did you mean |m|?"; m=-m; );
    if m == 1 then return poset({1}, {}); -- 1 is special
    M := toList \ toList factor m;
    p := local p;
    Pset := apply(#M, i-> p_i);
    R := QQ[Pset];
    numHash := hashTable apply(#M, i-> R_i=>first M_i);
    P := product apply(#M, p-> R_p^(last M_p));
    subFunc := apply(pairs numHash, q-> q_0=>q_1);
    Q := divisorPoset P;
    G := sort apply(Q.GroundSet, g-> sub(g, subFunc));
    L := apply(Q.Relations, g-> {sub(first g, subFunc), sub(last g, subFunc)});
    poset(G,L)
    )

--This method takes a pair of monomials: first element should divide second.
divisorPoset (RingElement, RingElement):= Poset =>(m, n) -> (
    if ring m === ring n then (
        if n % m === sub(0, ring m) then (
            P := divisorPoset (n//m);
            poset(apply(P.GroundSet, v -> v * m), apply(P.Relations, r -> (m * first r, m * last r)), P.RelationMatrix)
            ) else error "The first monomial does not divide the second."
        ) else error "The monomials must be in same ring."
    )

--This method takes a pair of exponent vectors a,b and computes divisorPoset x^a,x^b
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
    testmax := L -> min apply(L, j->#j) > 1;
    faceset := apply(flatten apply(toList(0..dim D), i-> toList flatten entries faces(i, D)), r -> support r);
    chainheads := apply(flatten entries facets D, i-> support i);
    maxchains := apply(chainheads, i-> {i});
    while any(maxchains, testmax) do (
        nextstage:={};
        holdover:=select(maxchains,c-> not testmax c);
        for m in select(maxchains,testmax) do (
            minsize:=min apply(m, i-> #i);
            minset:=first select(m, i-> #i == minsize);
            coveredfaces:=subsets(minset,minsize-1);
            nextstage=join(nextstage,apply(coveredfaces, c->append(m,c)))
            );
        maxchains = join(nextstage,holdover);
        );    
    poset(faceset, unique flatten apply(maxchains, i-> apply(subsets(i,2),reverse)))
    )

-- Hyperplane Arrangement Lattice: 
-- As written, this would most likely work for any type of arrangement lattice.
-- Given a set of linear forms defining the hyperplanes in the arrangement, returns set of intersection ideals.

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

-- input:  generators of a monomial ideal
-- output: lcm lattice of that monomial ideal
-- potential problem:  subsets dies when a set is too big (> 18)
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
    fn << "\\begin{document}" << endl << endl;
    fn << texPoset(P, opts) << endl;
    fn << "\\end{document}" << endl;
    close fn;
    get name
    )

texPoset = method(Options => {symbol SuppressLabels => posets'SuppressLabels, symbol Jitter => false})
texPoset (Poset) := String => opts -> (P) -> (
    if not instance(opts.SuppressLabels, Boolean) then error "The option SuppressLabels must be a Boolean.";
    if not instance(opts.Jitter, Boolean) then error "The option Jitter must be a Boolean.";
    C := maximalChains P;
    --hash table of variable labels:
    idx:= hashTable apply(#P.GroundSet, i-> P.GroundSet_i=> i);
    --edge list to be read into TikZ:
    edgelist:= apply(coveringRelations P, r-> concatenate(toString idx#(first r),"/",toString idx#(last r)));
    --height of poset:
    L := max apply(C, c-> #c) - 1;
    heightpairs := apply(P.GroundSet, g -> {g, L - max flatten apply(C, c-> positions(reverse c, i-> g === i))});
    protoH := partition(g-> last g, heightpairs);
    H := hashTable apply(keys protoH, k-> k=>apply(protoH#k, h-> first h));
    levelsets := apply(values H, v-> #v-1);
    scalew := min{1.5,15/ (1 + max levelsets)};
    scaleh := min{2/scalew,15/(L+1)};
    halflevelsets := apply(levelsets, j-> scalew*j/2.0);
    spacings := apply(toList(0..L), j-> scalew*toList(0..levelsets_j));
    -- The TeX String
    "\\begin{tikzpicture}[scale=1, vertices/.style={draw, fill=black, circle, inner sep=0pt}]\n" |
        concatenate(
            for i from 0 to L list for j from 0 to levelsets_i list
                {"\t\\node [vertices", if opts.SuppressLabels then "]" else (", label=right:{" | tex (values H)_i_j | "}]"),
                 " (",toString idx#((values H)_i_j),") at (-",toString halflevelsets_i,"+",
                 toString ((if opts.Jitter then random(scalew*0.2) else 0) + spacings_i_j),",",toString (scaleh*i),"){};\n"}
            ) |
    concatenate("\\foreach \\to/\\from in ", toString edgelist, "\n\\draw [-] (\\to)--(\\from);\n\\end{tikzpicture}\n")
    )

------------------------------------------
-- Vertices & vertex properties
------------------------------------------

-- input:  poset
-- output: list of elements covering minimal elements
atoms = method()
atoms Poset := List => P -> unique apply(select(coveringRelations P, R -> any(minimalElements P, elt -> (elt === R#0))), rels-> rels_1)

compare = method()
compare(Poset, Thing, Thing) := Boolean => (P,A,B) -> (
    Aindex := indexElement(P,A);
    Bindex := indexElement(P,B);
    P.RelationMatrix_Bindex_Aindex != 0
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

-- input: poset
-- output:  list of maximal elements
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

-- input:  poset
-- output:  meet irreducibles of poset
meetIrreducibles = method()
meetIrreducibles Poset := List => P -> (
    -- want to compute meets only for non-comparable elements
    if not isLattice P then error "The poset is not a lattice.";
    nonComparablePairs := select(subsets(P.GroundSet,2), posspair -> not compare(P, posspair#0,posspair#1) and not compare(P,posspair#1,posspair#0));
    meets := select(unique flatten apply(nonComparablePairs, posspair -> if meetExists(P, posspair#0, posspair#1) then posetMeet(P,posspair#0, posspair#1)), i -> i =!= null); 
    toList (set P.GroundSet - set meets)
    )

-- input:  poset
-- output:  list of minimal elements
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

-- iputs:  P a poset, and 2 elements of P.GroundSet
--outputs:  the element in P.GroundSet that is the meet of these, or "not comparable" or "not unique"
-- usage:  MeetExits used in isLattice
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


--input: P a poset and L a list of elements of the poset
--output: whether L is an antichain in P
isAntichain = method()
isAntichain (Poset, List) := Boolean => (P, L) -> (
    Q := subPoset(P, L);
    minimalElements(Q) == maximalElements(Q)
    )

-- Ported from Stembridge's Maple Package
linearExtensions = method()
linearExtensions Poset := List => P -> (
    if #P.GroundSet <= 1 then return {P.GroundSet};
    flatten apply(minimalElements P, m -> apply(linearExtensions dropElements(P, {m}), e -> prepend(m, e)))
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

-- Method given in Core
height Poset := ZZ => P -> -1 + max apply (maximalChains P, s-> #s)

-- P is atomic if every non-minimal, non-atom element is greater than some atom
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

-- Graded:  All maximal chains are the same length.
isGraded = method()
isGraded Poset := Boolean => P -> #unique apply(maximalChains P, c -> #c) == 1

--inputs: a poset P
--output:  boolean value for whether or not it is a lattice
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

-- Ranked:  There exists an integer ranking-function r on the groundset of P
--          such that for each x and y in P: if y covers x then r(y)-r(x) = 1.
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

---------
-- front page
---------
document { 
  Key => Posets,
  Headline => "a package for working with posets",
  PARA{},
  "The ", EM "Posets", " package defines Poset as a new data type and provides 
   routines which use or produce posets.  A poset or a partially ordered set 
   is a set together with a binary relation satisfying reflexivity, antisymmetry, and transitivity.",
  SUBSECTION "Contributors",
  "The following people have generously contributed code or worked on our code.",
  UL {
    {HREF("http://people.math.gatech.edu/~jyu67/Josephine_Yu/Main.html","Josephine Yu")},
    {HREF("http://www.math.purdue.edu/~nkummini/","Manoj Kumminni")},
    {HREF("http://www.math.cornell.edu/People/Grads/fisher.html","Kristine Fisher")},
    {HREF("http://www.mathstat.dal.ca/~handrew/","Andrew Hoefel")},
    {HREF("mailto:stephen.sturgeon@uky.edu", "Stephen Sturgeon")} 
    },
  }


--doc ///
--     Key
--           Posets
--     Headline
--          A package for working with posets. 
--     Description
--          Text
--           {\em Posets} package defines Poset as a new data type and provides 
--           routines which use or produce posets.   A poset or a partially ordered set is a set together with a binary relation satisfying reflexivity, antisymmetry, and transitivity.
--           Contributors
--           The following people have contributed code or have worked on this package.
--           {HREF("http://people.math.gatech.edu/~jyu67/Josephine_Yu/Main.html","Josephine Yu"")},     
           
--///
     
---------
-- types
----------           
doc ///
     Key
           Poset
     Headline
           a class for partially ordered sets (posets)
     Description
          Text
               This class is a type of HashTable which represents finite posets.  It consists of a ground 
               set, a set of sequences (a,b) representing relationships where a is less than or 
               equal to b, a matrix encoding these relations. 
      Example
          G = {a,b,c,d,e}; -- the ground set
          R = {(a,b),(b,c),(a,c),(a,d),(d,e)}; --a set of sequences representing relations that "generate" all other relations
          P = poset (G,R) -- the matrix encoding these relations is computed by calling this function       
     SeeAlso
          poset
          GroundSet
          Relations
          RelationMatrix       
///     

-------------
-- constructors
-------------

doc ///
     Key
           poset
      (poset, List, List)
      (poset, List, List, Matrix)
     Headline
           creating a poset
     Usage
       P = poset (G,R)
       P = poset (G,R,M)
     Inputs
      G : List 
           elements in the ground set of P
      R : List 
           sequences (a,b) which indicate that a is less than or equal to b
      M : Matrix
           with entries ij equal to one when the jth element in G is less than or equal to the ith element in G
     Outputs
      P : Poset
           a poset consisting of the elements in G, with the order relations determined by R 
           and or M
     Description
        Text
           This function allows one to create a poset by defining the set and giving the order relations between the elements in the set.
           The function assumes that each element in the defining list given is distinct, and operates by taking the transitive and reflexive 
            closure of the relations that it is given.  The function returns an error
            if the input relations are incompatible with creating a poset.
       Example
           G = {a,b,c,d};
            R = {(a,b), (a,c), (c,d)};
            P = poset (G,R)    
       Text
           Sometimes in finding "enough" relations one inadverdently finds all of the relations in the poset.  In this case, the user
        can bypass having the function poset calculate the transitive closure of the relations by entering the matrix encoding the
        relations in when calling the poset function.  In this scenario, the function does not check that the resulting object is 
        actually a poset because in order to do this, the function needs to compute the transitive closure of the relations and check
        that this matches the matrix given.  The purpose of entering a matrix is to bypass that computation.
       Example
           S = QQ[x,y,z];
        G = {x^2, x*y, z^2, x^2*y*z, x*y*z^3, x^2*y^2*z^3};
            R = select((flatten apply (G, g-> apply (G, h-> if h % g == 0 then (g,h)))), i -> i =!= null) -- finds all pairs where g divides h
        M = matrix apply (G, g-> apply (G, h-> if h % g == 0 then 1 else 0)) 
        P = poset(G,R,M) 
        
     SeeAlso
           Poset
      GroundSet
      Relations
      RelationMatrix
///
  
-----------
-- finding relations
-----------

doc ///
     Key
           transitiveClosure
      (transitiveClosure, List, List)
     Headline
           computes the transitive closure of a given set of relations.  
     Usage
           M = transitiveClosure(I,R)
     Inputs
      I : List
           ground set 
      R : List
           of pairs of elements in the ground set I.
     Outputs
      M : Matrix 
           whose (i,j) entry is 1 if (i,j) is a relation and 0 otherwise.
     Description
       Text
           This function uses the floydWarshall method from the Graphs package and is used by the poset constructor to compute RelationMatrix from Relations in a Poset.
       Example
           I = {a,b,c,d,e}; -- the ground set
           R = {(a,b),(b,c),(a,c),(a,d),(d,e)}; -- relations
                transitiveClosure(I,R)
     Caveat
        `       Output matrix is over RR.
     SeeAlso
           Poset
      poset
      Relations
      RelationMatrix
/// 
 
 
---------
-- poset routines
---------
 
doc ///
     Key
           compare
          (compare, Poset,Thing,Thing)
     Headline
          returns boolean value for whether an element is less than another 
     Usage
          compare(P,a,b)
     Inputs
           P : Poset
      a : Thing
      b : Thing
           a and b are elements of P
     Outputs
       true : Boolean
          if a is less than or equal to b
       false : Boolean
           otherwise
     Description
      Text
           This function simply looks at two elements in P, and determines what if any relation exists between them.
      Example
           P = poset ({a,b,c}, {(a,b), (a,c)});
           compare (P,a,c)
           compare (P,c,a)
           compare (P,b,c)
     Caveat
           Note that if two elements are not comparable, compare still returns a value of false.       
/// 
  
 
doc ///
     Key
           filter
          (filter,Poset,Thing)
     Headline
           returns a principal filter generated by the given element
     Usage 
           F = filter (P,a)
     Inputs
      P : Poset
      a : Thing
           a is an element of P
     Outputs
       F : List
           a list of all elements in P that are greater than or equal to a
     Description
       Example
           G = {a,b,c,d};
           R = {(a,b), (a,c), (c,d)};
           P = poset (G,R);
           F = filter (P,d)
     SeeAlso
           orderIdeal           
/// 

doc ///
     Key
           orderIdeal
          (orderIdeal, Poset, Thing)
     Headline
           returns a principal order ideal generated by the given element
     Usage 
           O = orderIdeal (P,a)
     Inputs
      P : Poset
      a : Thing
           a is an element of P
     Outputs
      O : List
           a list of all elements in P that are less than or equal to a
     Description
      Example
           G = {a,b,c,d};
           R = {(a,b), (a,c), (c,d)};
           P = poset (G,R);
           O = orderIdeal (P,c)
     SeeAlso
           filter    
/// 
 
 
doc ///
     Key
           posetMeet
      (posetMeet, Poset, Thing, Thing)
     Headline
           returns the meet of two elements
     Usage
          m = posetMeet (P,a,b)
     Inputs
           P : Poset
      a : Thing
      b : Thing
           a and b are in P
     Outputs
       m : Thing
           m is the meet of a and b in P
     Description 
       Text
           This function returns the greatest element that is less than both a and b in P.
      Example
           P = poset ({a,b,c,d,e,f}, {(a,d),(d,f),(b,d),(b,e),(c,e),(e,f)});
           posetMeet (P, d,e)
     Caveat
             This function returns an error if the meet does not exist.  To check if the meet exists use meetExists.
     SeeAlso
             meetExists
       posetJoin
       joinExists
/// 



doc ///
     Key
           posetJoin
      (posetJoin, Poset, Thing, Thing)
     Headline
           returns the join of two elements
     Usage
          j = posetJoin (P,a,b)
     Inputs
           P : Poset
      a : Thing
      b : Thing
           a and b are in P
     Outputs
      j : Thing
           j is the join of a and b in P
     Description 
      Text
           This function returns the least element that is greater than both a and b in P.
      Example
           P = poset ({a,b,c,d,e,f}, {(a,d),(d,f),(b,d),(b,e),(c,e),(e,f)});
           posetJoin (P, a,b)
     Caveat
             This function returns an error if the join does not exist.  To check if the join exists use joinExists.
     SeeAlso
             joinExists
       posetMeet
       meetExists
/// 
   
   
doc ///
     Key
           meetExists
      (meetExists, Poset, Thing, Thing)
     Headline
           determines if the meet exists
     Usage
          meetExists (P,a,b)
     Inputs
      P : Poset
      a : Thing
      b : Thing
           a and b are in P
     Outputs
      true : Boolean
           the meet of a and b in P exists
      false : Boolean
           otherwise
     Description 
      Text
          This function determines if greatest element that is less than both a and b in P exists.
      Example
           P = poset ({a,b,c,d,e,f}, {(a,d),(d,f),(b,d),(b,e),(c,e),(e,f)});
           meetExists (P,d,e)
                meetExists(P,a,b)
     Caveat
            If the meet exists, to find it use posetMeet.
     SeeAlso
             posetMeet
       posetJoin
       joinExists    
/// 

doc ///
     Key
           joinExists
      (joinExists, Poset, Thing,Thing)
     Headline
           determines if the join exists
     Usage
          joinExists (P,a,b)
     Inputs
      P : Poset
      a : Thing
      b : Thing
           a and b are in P
     Outputs
      true : Boolean
           the join of a and b in P exists
      false : Boolean
           otherwise
     Description 
      Text
           This function determines if least element that is greater than both a and b in P exists.
      Example
           P = poset ({a,b,c,d,e}, {(a,d),(b,d),(b,e),(c,e)});
           joinExists (P,d,e)
                joinExists(P,a,b)
     Caveat
            If the join exists, to find it use posetJoin.
     SeeAlso
       posetJoin
       posetMeet
       meetExists  
/// 
 
doc ///
     Key
      isLattice
      (isLattice,Poset)
     Headline
           determines if a poset is a lattice
     Usage
           isLattice (P)
     Inputs
           P: Poset
     Outputs
      true : Boolean
           if P is a lattice
      false : Boolean
           otherwise
     Description 
      Text
           This function examines the entire poset to determine whether or not every pair of elements has both a meet and a join.
      Example
           P = poset ({a,b,c,d,e,f}, {(a,d),(d,f),(b,d),(b,e),(c,e),(e,f)});
           isLattice (P)
      Text
           And by adding an element to the above example, we can create a poset which is a lattice.     
      Example
           P = poset ({a,b,c,d,e,f,x}, {(a,d),(d,f),(b,d),(b,e),(c,e),(e,f), (x,a), (x,b), (x,c)});   
               isLattice (P)       
    
/// 

     
---------
-- LCM lattices
---------

doc ///
     Key
           lcmLattice
      (lcmLattice,Ideal)
      (lcmLattice, MonomialIdeal)
     Headline
           returns the LCM lattice of an ideal
     Usage
           lcmLattice (I)
      lcmLattice (M)
     Inputs 
      I : Ideal
      M : MonomialIdeal
     Outputs
      L : Poset
     Description
      Text
           This command allows for fast computation of LCM lattices, which are particularly useful in the study of resolutions of monomial ideals.
           Specifically the LCM lattice is the set of all lcms of subsets of the generators of the ideal, partially ordered by divisability.  
      Example
           S = QQ[a,b,c,d];
           I = ideal (b^2-a*d, a*d-b*c, c^2-b*d);
           M = monomialIdeal (b^2, b*c, c^2);
           L = lcmLattice (I);
           L.GroundSet
           L.RelationMatrix
           LM = lcmLattice (M);
           LM.GroundSet
           LM.RelationMatrix
     Caveat           
           Note, that at present this command does not efficiently handle ideals with large numbers of generators.  This is a problem that should be
        fixed by the next release of this package.     
/// 

     
-----------------
-- divisorPoset
-----------------

doc ///
    Key
        divisorPoset
        (divisorPoset,RingElement)
    Headline
        returns the poset of all divisors of a given monomial
    Usage
        divisorPoset (M)
    Inputs 
        M : RingElement
    Outputs
        P : Poset
    Description
        Text
            This command computes the poset of all divisors of a given monomial. For two monomials,
            u and v with u strictly dividing v, we have u < v in this poset.
        Example
            S = QQ[a,b,c,d];
            P = divisorPoset(a*b^2*d^3)
/// 

     

-----------------
-- coveringRelations
-----------------

doc ///
    Key
        coveringRelations
        (coveringRelations,Poset)
    Headline
        returns a list of all relations (a < b) with no intermediates
    Usage
        coveringRelations (P)
    Inputs 
        P : Poset
    Outputs
        C : List
            all pairs (a,b) of elements of P where a < b and there is no c with a < c < b
    Description
        Text
            This command computes the list of all covering relations of a poset P. 
            A relation (a,b) is said to be a covering relation if a < b and there
            is no element c with a < c < b. The result of this method is cached.
        Example
            S = QQ[a,b,c,d];
            P = divisorPoset(a*b^2*d);
            P.GroundSet
            P.Relations
            C = coveringRelations P
/// 

-----------------
-- dropElements
-----------------

doc ///
    Key
        dropElements
        (dropElements,Poset,List)
        (dropElements,Poset,Function)
    Headline
        returns the poset obtained by removing a list of elements 
    Usage
        dropElements (P, L)
        dropElements (P, f)
    Inputs 
        P : Poset
        L : List
            elements of P
        f : Function
            boolean valued giving true on those elements to be removed
    Outputs
        Q : Poset
            on elements of P that are not in L (or for which f is false) and all induced relations
    Description
        Text
            This command take a poset P and returns a new poset that
            contains all elements in P that are not in L.
            The relations on the remaining elements are all relations that held in P.

            Alternately, if a boolean function is given as input instead of a list, all 
            elements for which the function returns true are removed from P.

        Example
            S = QQ[a,b];
            P = divisorPoset(a*b^2);
            P.GroundSet
            Q = dropElements(P, {a,a*b^2})
            R = dropElements(P, m -> first degree m === 2)
/// 

-----------------
-- maximalChains
-----------------

doc ///
    Key
        maximalChains
        (maximalChains,Poset)
    Headline
        returns all maximal chains of a poset
    Usage
        maximalChains (P)
    Inputs 
        P : Poset
    Outputs
        C : List
            of maximal chains of P
    Description
        Text
            The maximal chains of P are totally orders subsets of P which are not properly contained
            in any other totally ordered subsets.

            This method returns a list of all maximal chains. The maximal chains are themselves
            lists of elements in P ordered from smallest to largest.

            The results of this method are cached.

        Example
            S = QQ[a,b,c];
            P = divisorPoset(a*b^2*c);
            C = maximalChains P
/// 

-----------------
-- minimalElements
-----------------

doc ///
    Key
        minimalElements
        (minimalElements,Poset)
    Headline
        returns all minimal elements of a poset
    Usage
        minimalElements (P)
    Inputs 
        P : Poset
    Outputs
        L : List
            of all minimal elements of P
    Description
        Text
            This method returns a list of all minimal elements of P.
            The results of this method are cached.

        Example
            S = QQ[a,b,c];
            P = divisorPoset(a*b^2*c);
            minimalElements P
            Q = dropElements(P, minimalElements(P));
            minimalElements Q
/// 

-----------------
-- maximalElements
-----------------

doc ///
    Key
        maximalElements
        (maximalElements,Poset)
    Headline
        returns all maximal elements of a poset
    Usage
        maximalElements (P)
    Inputs 
        P : Poset
    Outputs
        L : List
            of all maximal elements of P
    Description
        Text
            This method returns a list of all maximal elements of P.
            The results of this method are cached.

        Example
            S = QQ[a,b,c];
            P = divisorPoset(a*b^2*c);
            maximalElements P
            Q = dropElements(P, maximalElements(P));
            maximalElements Q
/// 

-----------------
-- adjoinMax
-----------------

doc ///
    Key
        adjoinMax
        (adjoinMax,Poset)
        (adjoinMax,Poset,Thing)
    Headline
        returns new Poset with new maximal element
    Usage
        adjoinMax P
        adjoinMax(P,a)
    Inputs 
        P : Poset
        a : Thing
    Outputs
        Q : Poset
    Description
        Text
            This method returns a new poset with maximal element adjoined.
            If no element specified, uses {1}.

        Example
            G = {1,2,3,4}
            R = {{1,2},{1,3},{2,4},{3,4}}
            P = poset(G,R)
            Q = adjoinMax P
            Q = adjoinMax(P,5)
    SeeAlso
             adjoinMin
        maximalElements
        minimalElements
/// 

-----------------
-- adjoinMax
-----------------

doc ///
    Key
        adjoinMin
        (adjoinMin,Poset)
        (adjoinMin,Poset,Thing)
    Headline
        returns new Poset with new minimal element
    Usage
        adjoinMin P
        adjoinMin(P,a)
    Inputs 
        P : Poset
        a : Thing
    Outputs
        Q : Poset
    Description
        Text
            This method returns a new poset with minimal element adjoined.
            If no element specified, uses {0}.

        Example
            G = {1,2,3,4}
            R = {{1,2},{1,3},{2,4},{3,4}}
            P = poset(G,R)
            Q = adjoinMin P
            Q = adjoinMin(P,0)
    SeeAlso
             adjoinMax
        maximalElements
        minimalElements
/// 
-----------------
-- orderComplex
-----------------

doc ///
    Key
        orderComplex
        (orderComplex,Poset)
    Headline
        returns the simplicial complex with faces given by chains
    Usage
        orderComplex (P)
    Inputs 
        P : Poset
    Outputs
        D : SimplicialComplex
            the order complex of P
    Description
        Text
            This method returns the order complex of a poset P. The order
            complex is the simplicial complex whose faces are chains of P
            (and whose facets are maximal chains of P).

        Example
            S = QQ[a,b,c];
            P = divisorPoset(a*b*c);
            C = maximalChains P
            D = orderComplex P
/// 


-----------------
-- closedInterval
-----------------
doc ///
    Key
        closedInterval
        (closedInterval,Poset, Thing, Thing)
    Headline
        returns the closed interval in the poset between two elements
    Usage
        closedInterval(P,a,b)
    Inputs 
        P : Poset
        a : Thing
        b : Thing 
    Outputs
        I : Poset
            the closed interval between a and b 
    Description
        Text
             This routine returns the interval between the elements a and b in P, 
                     including a and b,
             and an error message if the two elements are not comparable in P.

        Example
             P = poset({a,b,c,d},{(a,b),(b,c),(b,d)});
             closedInterval(P,a,d)      
/// 

----------------
--openInterval
----------------

doc ///
    Key
        openInterval
        (openInterval,Poset,Thing,Thing)
    Headline
        returns the open interval in the poset between two elements
    Usage
        openInterval(P,a,b)
    Inputs
        P : Poset
        a : Thing
        b : Thing
    Outputs
        I : Poset
    Description
         Text
              This routine returns the intreval between the elements a and b in P, not including a and b,
              and an error message if the two elements are not comparable in P.
      
        Example
                     P = poset({a,b,c,d,e,f,g}, {(a,b), (a,c), (a,d), (b,e), (c,e), (c,f), (d,f), (e,g), (f,g)})
              openInterval(P,a,g)
///

-----------------
-- hasseDiagram
-----------------
doc  ///
    Key
              hasseDiagram
         (hasseDiagram,Poset)
    Headline
             returns Hasse diagram for the poset
    Usage
              hasseDiagram(P)
        Inputs
              P : Poset
        Outputs
         G : Digraph
              Directed graph whose edges correspond to covering relations in P
        Description
              Text 
              This routine returns the Hasse diagram which is a directed graph (defined in the Graphs package)
              whose edges correspond to the covering relations in P.  Specifically, the vertices in the graph 
              correspond to the elements in the ground set of P, and two vertices a and b have a directed edge 
              from a to b if a > b.
         Example
              P = poset ({a,b,c,d},{(a,b), (b,c), (b,d)})
              G = hasseDiagram(P)    
        SeeAlso
             displayGraph
///


-----------------
-- moebiusFunction
-----------------
doc///
     Key
           moebiusFunction
      (moebiusFunction,Poset)
     Headline
           returns the Moebius function values for the unique minimal element to each element of the poset
     Usage
           moebiusFunction(P)
     Inputs
           P : Poset
     Outputs
      M : HashTable
           Moebius function values for the minimal element of the poset to each element of the poset
     Description
       Text 
           This routine returns the Moebius function values for the unique minimal element to each element of the poset.
           If {\tt P} has more than one minimal element, an error will be signalled.
           In this example, $a$ is the minimal element of $P$; $M$ lists the Moebius function values from $a$ to each element of $P$.
      Example
           P = poset ({a,b,c,d},{(a,b), (b,c), (b,d)})
           M = moebiusFunction(P)    
     SeeAlso
           (moebiusFunction,Poset,Thing,Thing)
      Poset
///

doc///
     Key
      (moebiusFunction,Poset,Thing,Thing)
     Headline
           returns the Moebius function values for the minimal element of a closed interval to each element of the interval
     Usage
           moebiusFunction(P,a,b)
     Inputs
      P : Poset
      a : Thing
           a is an element of P
      b : Thing
           b is an element of P
     Outputs
       M : HashTable
           Moebius function values for the lesser of a and b to each element of the interval between a and b           
     Description
      Text
           For elements a and b of a poset P, this routine returns the Mobius function values for the minimal element in the closed 
           interval between elements a and b to each element of the interval between a and b. The routine handles both of the cases a<b and b<a.
      Example
           P = poset({a,b,c,d,e,f,g}, {(a,b), (a,c), (a,d), (b,e), (c,e), (c,f), (d,f), (e,g), (f,g)})
           moebiusFunction(P,b,g)
           moebiusFunction(P,g,b)           
     SeeAlso
           (moebiusFunction,Poset)
      Poset
///      

-----------------
-- subPoset
-----------------
doc///
     Key
           subPoset
      (subPoset,Poset,List)
     Headline
           returns the subposet supported on elements in a given list
     Usage
           subPoset(P,L)
     Inputs
      P : Poset
      L : List
           L consists of element in P
     Outputs
      Q : Poset
           subposet of P supported on elements in L           
     Description
        Text
               This command take a poset P and returns a new poset that
            contains all elements in P that are in L.
            The relations on the remaining elements are all relations that held in P.
      Example
           P = poset({a,b,c,d,e,f,g}, {(a,b), (a,c), (a,d), (b,e), (c,e), (c,f), (d,f), (e,g), (f,g)})
           subPoset(P, {a,e,g})           
     SeeAlso
          dropElements
///

-----------------
-- atoms
-----------------
doc///
     Key
           atoms
      (atoms,Poset)
     Headline
           returns the atoms of a poset
     Usage
           A = atoms(P)
     Inputs
           P : Poset
     Outputs
        A : List
          subset of the ground set of P consisting of elements covering minimal elements           
     Description
           Text
               This routine returns a list of elements which cover any minimal elements in P, these are known
                as the atoms of P.
      Example
           P = poset({a,b,c,d,e,f,g}, {(a,b), (a,c), (a,d), (b,e), (c,e), (c,f), (d,f), (e,g), (f,g)})
           atoms(P)           
///    


--------------
-- meetIrreducibles
--------------
doc///
     Key
           meetIrreducibles
      (meetIrreducibles,Poset)
     Headline
           returns the meet-irreducibles of a poset
     Usage
           L = meetIrreducibles(P)
     Inputs
           P : Poset
     Outputs
       L : List
          subset of the ground set of P consisting of meet-irreducible elements           
     Description
       Text
               An element a of a poset P is meet irreducible if it is not the meet of any set of elements (not containing a).  
                This routine returns a list of all such elements in the poset P.  
      Example
           P = poset({a,b,c,d,e,f,g}, {(a,b), (a,c), (a,d), (b,e), (c,e), (c,f), (d,f), (e,g), (f,g)})
           meetIrreducibles(P)           
///



doc ///
     Key 
           GroundSet
     Headline
           underlying set of a poset
     Usage
           G = P.GroundSet
     Inputs
           P : Poset
     Outputs
        G : List
           list of elements in P without the data of how they are partially ordered
     Description
           Text
                Since any poset is in fact a HashTable this symbol denotes the data in the HashTable consisting of the elements of the set.
      Example
           S = QQ[a,b,c,d];
           M = monomialIdeal (b^2, b*c, c^2);
           L = lcmLattice (M);
           L.GroundSet
     SeeAlso
           RelationMatrix
      Relations
      poset
      Poset
///
 
 
doc ///
     Key 
           RelationMatrix
     Headline
           the matrix expressing all of the relations between elements in a Poset
     Usage
           M = P.RelationMatrix
     Inputs
           P : Poset
     Outputs
        M : Matrix
           where the ijth entry indicates whether or not the jth element in the set is less than or equal to the ith element
     Description
           Text
                Since any poset is in fact a HashTable this symbol denotes the data in the HashTable containing all possible relations between elements.
      Example
           S = QQ[a,b,c,d];
           M = monomialIdeal (b^2, b*c, c^2);
           L = lcmLattice (M);
           L.GroundSet
           L.RelationMatrix
     SeeAlso
           GroundSet
      Relations
      poset
      Poset
/// 
 
doc ///
     Key 
           Relations
     Headline
           a set of relations in the poset that generates all other relations
     Usage
           R = P.Relations
     Inputs
           P : Poset
     Outputs
           R : List
            list of pairs of elements in P where (a,b) means a is less than or equal to b
     Description
           Text
                Since any poset is in fact a HashTable this symbol denotes the data in the HashTable which will describe all of the relations
            between elements in P.
      Example
           P = poset ({a,b,c,d,e,f},{(a,d),(d,f),(b,d),(b,e),(c,e),(e,f)});
           P.Relations --note there is not a one to one correspondence between these and entries in the RelationMatrix
           P.RelationMatrix
     Caveat
           Typically, the relations are the data entered in by the user and by no means account for every relation.  The RelationMatrix is usually computed
       from this set and thus is a better descriptor of the relations in P.
     SeeAlso
           RelationMatrix
      GroundSet
      poset
      Poset
///

doc///
     Key
           isAntichain
      (isAntichain, Poset, List)
     Headline
           checks whether a subposet is an anti-chain
     Usage
           isAntichain(P, L)
     Inputs
         P : Poset
         L : List
           a list of elements of P 
     Outputs
          true : Boolean
               if L is an antichain in P
         false : Boolean
             otherwise
     Description
           Text
            This function determines whether a list of elements of a poset is an anti-chain.
             
      Example
           P2 = poset({a,b,c,d,e,f,g}, {(a,b), (a,c), (a,d), (b,e), (c,e), (c,f), (d,f), (e,g), (f,g)})
           isAntichain(P2, {a,b})     
           isAntichain(P2, {b,c,d}) 
///

doc///
     Key
           intersectionLattice
        (intersectionLattice, List, Ring)
     Headline
           computes intersection lattice of an arrangement
     Usage
           intersectionLattice(H,R)
     Inputs
         H : List
             a list of elements of R
         R : PolynomialRing 
     Outputs
          P : Poset
     Description
      Text
           Given a set of equations f defining hyperplanes or hypersurfaces,
           computes the intersection lattice of the f.
          
      Example
           R=QQ[x,y]
           H={y+x,y-x,y-x-1,y}
           L=intersectionLattice(H,R)
      Text
           This code will produce intersection arrangement for hypersurfaces.
      Example
           R=QQ[x,y,z]
           H={x^2+y^2+z^2-9, z-1, x,y}
           L=intersectionLattice(H,R)
     SeeAlso
           projectivizeArrangement
           
///     

------------------------------------------
-- )Tests
------------------------------------------

-- TEST 0
-- a lattice, B_3
TEST ///
I ={a,b,c,d,e,f,g,h};
C ={(a,b),(a,c),(a,d),(b,e),(b,f),(c,e),(c,g),(d,f),(d,g),(e,h),(f,h),(g,h)};
P=poset(I,C);
M = matrix {{1,1,1,1,1,1,1,1},
        {0,1,0,0,1,1,0,1},
        {0,0,1,0,1,0,1,1},
        {0,0,0,1,0,1,1,1},
        {0,0,0,0,1,0,0,1},
        {0,0,0,0,0,1,0,1},
        {0,0,0,0,0,0,1,1},
        {0,0,0,0,0,0,0,1}};
assert (entries P.RelationMatrix == entries M)
assert (posetJoin(P,a,b) == {b})
assert (posetJoin(P,b,d) == {f})
assert (posetMeet(P,a,b) == {a})
assert (posetMeet(P,f,g) == {d})
assert (filter(P,a) == {a,b,c,d,e,f,g,h})
assert (filter(P,b) == {b,e,f,h})
assert (orderIdeal(P,a) == {a})
assert (orderIdeal(P,g) == {a,c,d,g})
assert (isLattice(P))
///


-- TEST 1
-- two equivllaent non lattices with different initial data
TEST ///
I1={a,b,c,d,e,f};
C1={(a,c),(a,d),(b,c),(b,d),(c,e),(d,e),(e,f)};
P1=poset(I1,C1);

--Poset P1 with additional relations (a,e) and (a,f) added
I2={a,b,c,d,e,f};
C2={(a,c),(a,d),(b,c),(b,d),(c,e),(d,e),(a,e),(a,f),(e,f)};
P2=poset(I2,C2);

assert (P1.RelationMatrix == P2.RelationMatrix)    
assert (orderIdeal(P1,b) == {b})
assert (orderIdeal(P1,c) == {a,b,c})
assert (filter (P1,b) == {b,c,d,e,f})
assert (isLattice (P1) == false)
-- do joins and meets
///

-- do an LCM lattice
-- do order ideal

-- TEST 2
-- failing test commented out by dan:
-- TEST ///
-- V = {a,b,c,d,e};
-- E = {(a,b),(a,d),(b,c),(b,e),(c,e),(d,e)};
-- G = poset (V,E);
-- A = adjacencyMatrix(G);
-- D = allPairsShortestPath(A);
-- T = transitiveClosure(V,E);

-- assert(A_(0,1)==1 and A_(0,3)==1 and A_(1,2)==1 and A_(1,4)==1 and A_(2,4)==1 and A_(3,4)==1)
-- assert(D_(0,4)==2 and D_(4,0)==1/0. and D_(3,3)==0)
-- --assert(T== promote(matrix {{1, 1, 1, 1, 1}, {0, 1, 1, 0, 1}, {0, 0, 1, 0, 1}, {0, 0, 0, 1, 1}, {0, 0, 0, 0, 1}}, RR))

-- D1 =allPairsShortestPath(matrix({{0,1,1/0.,4},{1/0.,0,1/0.,2},{1,1/0.,0,1/0.},{1/0.,1/0.,1,0}})); -- digraph with a cycle
-- assert(D1 ==  promote(matrix {{0, 1, 4, 3}, {4, 0, 3, 2}, {1, 2, 0, 4}, {2, 3, 1, 0}}, RR))

-- ///


-- TEST 3
TEST ///
P1 = poset ({a,b,c,d},{(a,b), (b,c), (b,d)});
P2 = poset({a,b,c,d,e,f,g}, {(a,b), (a,c), (a,d), (b,e), (c,e), (c,f), (d,f), (e,g), (f,g)});
R = QQ[x,y,z,w];
I = ideal(x^2, x*y, y^3, y*z);
L = lcmLattice I;
M = new HashTable from {x^2*y^3*z => 0, y^3*z => 1, x^2*y*z => 0, y^3 => -1, x*y^3*z => -1, y*z => -1, x^2 => -1,
      x*y => -1, x*y^3 => 1, x^2*y^3 => 0, 1 => 1, x^2*y => 1, x*y*z => 1}; 

assert ((moebiusFunction L)#(x^2*y^3) === M#(x^2*y^3)) 
assert ((moebiusFunction L)#(x*y*z) === M#(x*y*z)) 
assert( (moebiusFunction(P2, b,g)) === new HashTable from {e => -1, b => 1, g => 0} )
assert( (moebiusFunction(P1)) === new HashTable from {a => 1, b => -1, c => 0, d => 0} )
///

-- TEST 4
TEST ///
R = QQ[x,y,z];
L = lcmLattice ideal (x^2, y^2, z^2);
L2 = divisorPoset(x^2*y^3);

--testing divisorPoset and LCM lattices
assert( (L.GroundSet) == {1,z^2,y^2,y^2*z^2,x^2,x^2*z^2,x^2*y^2,x^2*y^2*z^2} )
assert( allRelations L == {{1,1},{1,z^2},{1,y^2},{1,y^2*z^2},{1,x^2},{1,x^2*z^2},{1,x^2*y^2},{1,x^2*y^2*z^2},{z^2,z^2},{z^2,y^2*z^2},{z^2,x^2*z^2},{z^2,x^2*y^2*z^2},{y^2,y^2},{y^2,y^2*z^2},{y^2,x^2*y^2},{y^2,x^2*y^2*z^2},{y^2*z^2,y^2*z^2},{y^2*z^2,x^2*y^2*z^2},{x^2,x^2},{x^2,x^2*z^2},{x^2,x^2*y^2},{x^2,x^2*y^2*z^2},{x^2*z^2,x^2*z^2},{x^2*z^2,x^2*y^2*z^2},{x^2*y^2,x^2*y^2},{x^2*y^2,x^2*y^2*z^2},{x^2*y^2*z^2,x^2*y^2*z^2}} )
assert( (L.RelationMatrix) === map(ZZ^8,ZZ^8,{{1, 1, 1, 1, 1, 1, 1, 1}, {0, 1, 0, 1, 0, 1, 0, 1}, {0, 0, 1, 1, 0, 0, 1, 1}, {0, 0, 0, 1, 0, 0, 0, 1}, {0, 0, 0, 0, 1, 1, 1, 1}, {0, 0, 0, 0, 0, 1, 0, 1}, {0, 0, 0, 0, 0, 0, 1, 1}, {0, 0, 0, 0, 0, 0, 0, 1}}) )
assert( (L2.GroundSet) == {1,y,y^2,y^3,x,x*y,x*y^2,x*y^3,x^2,x^2*y,x^2*y^2,x^2*y^3} )
assert( allRelations L2 == {{1,1},{1,y},{1,y^2},{1,y^3},{1,x},{1,x*y},{1,x*y^2},{1,x*y^3},{1,x^2},{1,x^2*y},{1,x^2*y^2},{1,x^2*y^3},{y,y},{y,y^2},{y,y^3},{y,x*y},{y,x*y^2},{y,x*y^3},{y,x^2*y},{y,x^2*y^2},{y,x^2*y^3},{y^2,y^2},{y^2,y^3},{y^2,x*y^2},{y^2,x*y^3},{y^2,x^2*y^2},{y^2,x^2*y^3},{y^3,y^3},{y^3,x*y^3},{y^3,x^2*y^3},{x,x},{x,x*y},{x,x*y^2},{x,x*y^3},{x,x^2},{x,x^2*y},{x,x^2*y^2},{x,x^2*y^3},{x*y,x*y},{x*y,x*y^2},{x*y,x*y^3},{x*y,x^2*y},{x*y,x^2*y^2},{x*y,x^2*y^3},{x*y^2,x*y^2},{x*y^2,x*y^3},{x*y^2,x^2*y^2},{x*y^2,x^2*y^3},{x*y^3,x*y^3},{x*y^3,x^2*y^3},{x^2,x^2},{x^2,x^2*y},{x^2,x^2*y^2},{x^2,x^2*y^3},{x^2*y,x^2*y},{x^2*y,x^2*y^2},{x^2*y,x^2*y^3},{x^2*y^2,x^2*y^2},{x^2*y^2,x^2*y^3},{x^2*y^3,x^2*y^3}} )
assert( (L2.RelationMatrix) === map(ZZ^12,ZZ^12,{{1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1}, {0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1}, {0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1}, {0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1}, {0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1}, {0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1}, {0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1}, {0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1}, {0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1}, {0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1}, {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1}, {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1}}) )
///


-- TEST 5
-- failing test commented out by dan:
-- TEST ///
-- P1 = poset({a,b,c,d,e},{(a,c),(a,d),(b,c),(b,d),(c,e),(d,e)});
-- R = QQ[x,y,z];
-- L = lcmLattice ideal (x^2, y^2, z^2);

-- -- testing hasseDiagram
-- assert((hasseDiagram P1)#a === set {})
-- assert((hasseDiagram P1)#b === set {})
-- assert((hasseDiagram P1)#c === set {a,b})
-- assert((hasseDiagram P1)#d === set {a,b})
-- assert((hasseDiagram P1)#e === set {c,d})
-- assert( toString sort pairs (hasseDiagram L) === toString sort pairs new Digraph from {x^2*y^2*z^2 => new Set from {x^2*y^2, x^2*z^2, y^2*z^2}, x^2*y^2 => new Set from {x^2, y^2}, x^2*z^2 => new Set from {x^2, z^2}, x^2 => new Set from {1}, y^2*z^2 => new Set from {y^2, z^2}, 1 => new Set from {}, z^2 => new Set from {1}, y^2 => new Set from {1}} )

-- ///

-- TEST 6
TEST ///
P1 = poset({a,b,c,d,e},{(a,c),(a,d),(b,c),(b,d),(c,e),(d,e)});
R = QQ[x,y,z];
L = lcmLattice ideal (x^2, y^2, z^2);
--testing max/min elts
assert( (maximalElements P1) === {e} )
assert( (maximalElements L) === {x^2*y^2*z^2} )
assert( (minimalElements P1) === {a,b} )
assert( (minimalElements L) == {1} )

--testing atoms
assert( (atoms(P1) ) === {c,d} )
assert( (atoms(L)) === {x^2,z^2,y^2} )
///

-- TEST 7
TEST /// 
P1 = poset({a,b,c,d,e},{(a,c),(a,d),(b,c),(b,d),(c,e),(d,e)});
P2 = poset({a,b,c,d,e,f,g,h},{(h,a),(h,b),(h,c),(h,d),(a,e),(b,e),(e,f),(c,f),(f,g),(d,g)});
R = QQ[x,y,z];
L = lcmLattice ideal (x^2, y^2, z^2);
L2 = divisorPoset(x^2*y^3);

--testing subPoset
assert( ((subPoset(P1, {a,b,e})).GroundSet) === {a,b,e} )
assert( ((subPoset(P1, {a,b,e})).Relations) === {{a,e},{b,e}} )
assert( ((subPoset(P1, {a,b,e})).RelationMatrix) === map(ZZ^3,ZZ^3,{{1, 0, 1}, {0, 1, 1}, {0, 0, 1}}) )
assert( ((subPoset(P2, {a,e,f,d})).GroundSet) === {a,d,e,f} )
assert( ((subPoset(P2, {a,e,f,d})).Relations) === {{a,e},{a,f},{e,f}} )
assert( ((subPoset(P2, {a,e,f,d})).RelationMatrix) === map(ZZ^4,ZZ^4,{{1, 0, 1, 1}, {0, 1, 0, 0}, {0, 0, 1, 1}, {0, 0, 0, 1}}) )
assert( ((subPoset(L, {x^2,y^2,x^2*y^2})).GroundSet) === {y^2,x^2,x^2*y^2} )
assert( ((subPoset(L, {x^2,y^2,x^2*y^2})).Relations) === {{y^2,x^2*y^2},{x^2,x^2*y^2}} )
assert( ((subPoset(L, {x^2,y^2,x^2*y^2})).RelationMatrix) === map(ZZ^3,ZZ^3,{{1, 0, 1}, {0, 1, 1}, {0, 0, 1}}) )

-- testing dropElements
assert( ((dropElements(P1, {a,c})).GroundSet) === {b,d,e} )
assert( ((dropElements(P1, {a,c})).Relations) === {{b,d},{b,e},{d,e}} )
assert( ((dropElements(P1, {a,c})).RelationMatrix) === map(ZZ^3,ZZ^3,{{1, 1, 1}, {0, 1, 1}, {0, 0, 1}}) )
assert( ((dropElements(L2, m-> first degree m > 2)).GroundSet) == {1,y,y^2,x,x*y,x^2} )
assert( ((dropElements(L2, m-> first degree m > 2)).Relations) == {{1,y}, {1,y^2}, {1,x}, {1,x*y}, {1,x^2}, {y,y^2}, {y,x*y}, {x,x*y}, {x,x^2}} )
assert( ((dropElements(L2, m-> first degree m > 2)).RelationMatrix) === map(ZZ^6,ZZ^6,{{1, 1, 1, 1, 1, 1}, {0, 1, 1, 0, 1, 0}, {0, 0, 1, 0, 0, 0}, {0, 0, 0, 1, 1, 1}, {0, 0, 0, 0, 1, 0}, {0, 0, 0, 0, 0, 1}}) )

///


-- TEST 8
TEST ///
P1 = poset({a,b,c,d,e},{(a,c),(a,d),(b,c),(b,d),(c,e),(d,e)});
R = QQ[x,y,z];
L = lcmLattice ideal (x^2, y^2, z^2);

S = QQ[v_0..v_4]
T = QQ[v_0..v_7]
assert( toString ((orderComplex P1).facets) === toString (use S; map(S^1,S^{{-3},{-3},{-3},{-3}},{{v_1*v_3*v_4, v_0*v_3*v_4, v_1*v_2*v_4, v_0*v_2*v_4}})) )
assert( toString ((orderComplex L).facets) === toString (use T; map(T^1,T^{{-4},{-4},{-4},{-4},{-4},{-4}},{{v_0*v_4*v_6*v_7, v_0*v_2*v_6*v_7, v_0*v_4*v_5*v_7, v_0*v_1*v_5*v_7, v_0*v_2*v_3*v_7, v_0*v_1*v_3*v_7}})) )
///

-- TEST 9
TEST ///
P1 = poset ({h,i,j,k},{(h,i), (i,j), (i,k)})
P2 = poset({a,b,c,d,e,f,g}, {(a,b), (a,c), (a,d), (b,e), (c,e), (c,f), (d,f), (e,g), (f,g)})
R = QQ[x,y,z,w]
I = ideal(x^2, x*y, y^3, y*z)
L = lcmLattice I
assert( (isAntichain(P1, {j, k})) === true )
assert( (isAntichain(P1, {j, k, h})) === false )
assert( (isAntichain(P2, {a, b, g})) === false )
assert( (isAntichain(P2, {b, c, d})) === true )
assert( (isAntichain(L, {y*z, y^3, x*y})) === true )
assert( (isAntichain(L, {y*z, x^2*y, x*y*x})) === true )
///


-- TEST 10
TEST ///
P1 = poset ({h,i,j,k},{(h,i), (i,j), (i,k)});
P2 = poset({a,b,c,d,e,f,g}, {(a,b), (a,c), (a,d), (b,e), (c,e), (c,f), (d,f), (e,g), (f,g)});
R = QQ[x,y,z,w];
I = ideal(x^2, x*y, y^3, y*z);
L = lcmLattice I;

assert( (maximalChains(P1)) === {{h,i,j},{h,i,k}} )
assert( (maximalChains(P2)) === {{a,b,e,g},{a,c,e,g},{a,c,f,g},{a,d,f,g}})
assert( (sort maximalChains(L)) == {{1, y*z, x*y*z, x^2*y*z, x^2*y^3*z}, {1, y*z, x*y*z, x*y^3*z, x^2*y^3*z},
        {1, y*z, y^3*z, x*y^3*z, x^2*y^3*z}, {1, x*y, x*y*z, x^2*y*z, x^2*y^3*z}, {1, x*y, x*y*z, x*y^3*z, x^2*y^3*z},
        {1, x*y, x^2*y, x^2*y*z, x^2*y^3*z}, {1, x*y, x^2*y, x^2*y^3, x^2*y^3*z}, {1, x*y, x*y^3, x*y^3*z, x^2*y^3*z}, 
        {1, x*y, x*y^3, x^2*y^3, x^2*y^3*z}, {1, x^2, x^2*y, x^2*y*z, x^2*y^3*z}, {1, x^2, x^2*y, x^2*y^3, x^2*y^3*z},
        {1, y^3, y^3*z, x*y^3*z, x^2*y^3*z}, {1, y^3, x*y^3, x*y^3*z, x^2*y^3*z}, {1, y^3, x*y^3, x^2*y^3, x^2*y^3*z}} )
///

-- TEST 11
TEST ///
P1 = poset ({h,i,j,k},{(h,i), (i,j), (i,k)});
P2 = poset({a,b,c,d,e,f,g}, {(a,b), (a,c), (a,d), (b,e), (c,e), (c,f), (d,f), (e,g), (f,g)});
R = QQ[x,y,z,w];
I = ideal(x^2, x*y, y^3, y*z);
L = lcmLattice I;


meetIrreducibles L
assert( (try meetIrreducibles P1  else oops) === oops )
assert( set meetIrreducibles P2 === set {e,f,g,b,d} )
assert( (set meetIrreducibles L) === set {x^2, y^3*z, x*y^3*z, x^2*y*z, x^2*y^3, x^2*y^3*z} )
///

-- TEST 12
TEST ///
P1 = poset ({h,i,j,k},{(h,i), (i,j), (i,k)});
P2 = poset({a,b,c,d,e,f,g}, {(a,b), (a,c), (a,d), (b,e), (c,e), (c,f), (d,f), (e,g), (f,g)});
R = QQ[x,y,z,w];
I = ideal(x^2, y^2, z^2);
L = lcmLattice I;
assert( (coveringRelations P1) === {{h,i},{i,j},{i,k}} )
assert( (coveringRelations P2) === {{a,b},{a,c},{a,d},{b,e},{c,e},{c,f},{d,f},{e,g},{f,g}} )
assert( (sort coveringRelations L) == {{1, z^2}, {1, y^2}, {1, x^2}, {z^2, y^2*z^2}, {z^2, x^2*z^2}, {y^2, y^2*z^2}, {y^2, x^2*y^2}, 
        {x^2, x^2*z^2}, {x^2, x^2*y^2}, {y^2*z^2, x^2*y^2*z^2}, {x^2*z^2, x^2*y^2*z^2}, {x^2*y^2, x^2*y^2*z^2}} )
///

-- TEST 13
TEST ///
P1 = poset ({h,i,j,k},{(h,i), (i,j), (i,k)});
P2 = poset({a,b,c,d,e,f,g}, {(a,b), (a,c), (a,d), (b,e), (c,e), (c,f), (d,f), (e,g), (f,g)});

assert( ((openInterval(P1,h,j)).Relations) === {} )
assert( sort ((closedInterval(P1,i,k)).Relations) === {{i,k}} )
assert( sort ((openInterval(P2,a,e)).Relations) === {} )
assert( sort ((closedInterval(P2,c,g)).Relations) === {{c,e},{c,f},{c,g},{e,g},{f,g}} )

///

-- TEST 14
--TEST ///
--B = booleanLattice(2)   
--assert( toString (B.GroundSet) === toString {1,x_2,x_1,x_1*x_2} )
--assert( (B.RelationMatrix) === map(ZZ^4,ZZ^4,{{1, 1, 1, 1}, {0, 1, 0, 1}, {0, 0, 1, 1}, {0, 0, 0, 1}}) )
--assert( toString (B.Relations) === toString {(1,1),(1,x_2),(1,x_1),(1,x_1*x_2),(x_2,x_2),(x_2,x_1*x_2),(x_1,x_1),(x_1, x_1*x_2),(x_1*x_2,x_1*x_2)} )
--///


end;


loadPackage("Posets",FileName=>"./Posets.m2")
